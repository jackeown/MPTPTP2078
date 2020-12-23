%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:36 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  200 (1389 expanded)
%              Number of clauses        :  116 ( 478 expanded)
%              Number of leaves         :   24 ( 295 expanded)
%              Depth                    :   23
%              Number of atoms          :  757 (6176 expanded)
%              Number of equality atoms :  212 ( 702 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f18,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v1_subset_1(X2,u1_struct_0(X0))
                <=> v1_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v1_subset_1(X2,u1_struct_0(X0))
              <=> v1_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v1_subset_1(X2,u1_struct_0(X0))
                  | ~ v1_tex_2(X1,X0) )
                & ( v1_tex_2(X1,X0)
                  | ~ v1_subset_1(X2,u1_struct_0(X0)) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(X2,u1_struct_0(X0))
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK2),X0) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | v1_tex_2(k1_tex_2(X0,X1),X0) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | ~ v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1))
            | v1_tex_2(k1_tex_2(sK1,X1),sK1) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f55,f57,f56])).

fof(f89,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f86,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK0(X0),X0)
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK0(X0),X0)
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f50])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f63,plain,(
    ! [X0] : ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f66,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ~ v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) )
           => ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
          | v1_subset_1(X1,u1_struct_0(X0))
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | v1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ~ v2_struct_0(X1)
           => ( ~ v1_tex_2(X1,X0)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4044,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_4043,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4491,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4044,c_4043])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_918,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_25])).

cnf(c_919,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_4026,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_subset_1(k6_domain_1(X1,X0),X1) = iProver_top
    | v1_zfmisc_1(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_919])).

cnf(c_23,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_168,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_9])).

cnf(c_169,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_168])).

cnf(c_26,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_236,plain,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_26])).

cnf(c_639,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_169,c_236])).

cnf(c_640,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_639])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_642,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_640,c_29])).

cnf(c_643,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_642])).

cnf(c_4029,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_31,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_641,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_18,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1875,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_1876,plain,
    ( m1_pre_topc(k1_tex_2(X0,sK2),X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1875])).

cnf(c_1877,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(X0,sK2),X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1876])).

cnf(c_1879,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1877])).

cnf(c_3415,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_3426,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3415])).

cnf(c_3407,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3432,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3407])).

cnf(c_5192,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4029,c_31,c_32,c_641,c_1879,c_3426,c_3432])).

cnf(c_5198,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4026,c_5192])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5299,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5198,c_33])).

cnf(c_5536,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4491,c_5299])).

cnf(c_5839,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5536,c_31,c_32,c_1879,c_3426,c_3432])).

cnf(c_4,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4046,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4409,plain,
    ( sK0(X0) = X0
    | v1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4046,c_4043])).

cnf(c_3,plain,
    ( ~ v1_subset_1(sK0(X0),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_90,plain,
    ( v1_subset_1(sK0(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5072,plain,
    ( sK0(X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4409,c_90])).

cnf(c_5077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5072,c_4046])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_437,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_438,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_4031,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_subset_1(X0,u1_struct_0(X1)) = iProver_top
    | v7_struct_0(X1) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_zfmisc_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_6231,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | v7_struct_0(X0) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5077,c_4031])).

cnf(c_7,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_401,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_5,c_7])).

cnf(c_402,plain,
    ( v2_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_6486,plain,
    ( v7_struct_0(X0) = iProver_top
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6231,c_402])).

cnf(c_6487,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | v7_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6486])).

cnf(c_2,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4048,plain,
    ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_4062,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4048,c_1])).

cnf(c_6497,plain,
    ( v7_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6487,c_4062])).

cnf(c_6503,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
    | v7_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5839,c_6497])).

cnf(c_8,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_79,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_81,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_79])).

cnf(c_84,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_86,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_189,plain,
    ( ~ l1_struct_0(X1)
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | v1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_zfmisc_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_0])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | v1_zfmisc_1(X0)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_190])).

cnf(c_414,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(X0,u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_4032,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v1_subset_1(X0,u1_struct_0(X1)) = iProver_top
    | v7_struct_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_414])).

cnf(c_5905,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5077,c_4032])).

cnf(c_905,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(X1)
    | u1_struct_0(X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_401])).

cnf(c_906,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(unflattening,[status(thm)],[c_905])).

cnf(c_907,plain,
    ( v2_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_906])).

cnf(c_5980,plain,
    ( v7_struct_0(X0) != iProver_top
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5905,c_907])).

cnf(c_5981,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
    | v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5980])).

cnf(c_5990,plain,
    ( v7_struct_0(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5981,c_4062])).

cnf(c_10,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_238,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
    inference(prop_impl,[status(thm)],[c_27])).

cnf(c_673,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK1,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_238])).

cnf(c_674,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_673])).

cnf(c_676,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v7_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_674,c_30,c_29])).

cnf(c_4027,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v7_struct_0(sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_678,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v7_struct_0(sK1) != iProver_top
    | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1911,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_1912,plain,
    ( v2_struct_0(X0)
    | ~ v2_struct_0(k1_tex_2(X0,sK2))
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1911])).

cnf(c_1913,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k1_tex_2(X0,sK2)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1912])).

cnf(c_1915,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1913])).

cnf(c_5001,plain,
    ( v7_struct_0(sK1) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4027,c_31,c_32,c_678,c_1879,c_1915,c_3426,c_3432])).

cnf(c_5002,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v7_struct_0(sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5001])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4038,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_subset_1(k6_domain_1(X1,X0),X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_zfmisc_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5007,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | v7_struct_0(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5002,c_4038])).

cnf(c_5184,plain,
    ( v7_struct_0(sK1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5007,c_31,c_32,c_33,c_81,c_86])).

cnf(c_5994,plain,
    ( v7_struct_0(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5990,c_5184])).

cnf(c_6499,plain,
    ( v7_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6497])).

cnf(c_6522,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6503,c_31,c_32,c_81,c_86,c_5839,c_5994,c_6499])).

cnf(c_6548,plain,
    ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6522,c_5990])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_4455,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4456,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4455])).

cnf(c_4458,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4456])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1893,plain,
    ( v7_struct_0(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_1894,plain,
    ( v7_struct_0(k1_tex_2(X0,sK2))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1893])).

cnf(c_1895,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | v7_struct_0(k1_tex_2(X0,sK2)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1897,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6548,c_6499,c_5994,c_4458,c_3432,c_3426,c_1897,c_1879,c_86,c_81,c_32,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.06/0.99  
% 2.06/0.99  ------  iProver source info
% 2.06/0.99  
% 2.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.06/0.99  git: non_committed_changes: false
% 2.06/0.99  git: last_make_outside_of_git: false
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     num_symb
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       true
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  ------ Parsing...
% 2.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.06/0.99  ------ Proving...
% 2.06/0.99  ------ Problem Properties 
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  clauses                                 25
% 2.06/0.99  conjectures                             3
% 2.06/0.99  EPR                                     4
% 2.06/0.99  Horn                                    16
% 2.06/0.99  unary                                   7
% 2.06/0.99  binary                                  2
% 2.06/0.99  lits                                    74
% 2.06/0.99  lits eq                                 2
% 2.06/0.99  fd_pure                                 0
% 2.06/0.99  fd_pseudo                               0
% 2.06/0.99  fd_cond                                 0
% 2.06/0.99  fd_pseudo_cond                          1
% 2.06/0.99  AC symbols                              0
% 2.06/0.99  
% 2.06/0.99  ------ Schedule dynamic 5 is on 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ 
% 2.06/0.99  Current options:
% 2.06/0.99  ------ 
% 2.06/0.99  
% 2.06/0.99  ------ Input Options
% 2.06/0.99  
% 2.06/0.99  --out_options                           all
% 2.06/0.99  --tptp_safe_out                         true
% 2.06/0.99  --problem_path                          ""
% 2.06/0.99  --include_path                          ""
% 2.06/0.99  --clausifier                            res/vclausify_rel
% 2.06/0.99  --clausifier_options                    --mode clausify
% 2.06/0.99  --stdin                                 false
% 2.06/0.99  --stats_out                             all
% 2.06/0.99  
% 2.06/0.99  ------ General Options
% 2.06/0.99  
% 2.06/0.99  --fof                                   false
% 2.06/0.99  --time_out_real                         305.
% 2.06/0.99  --time_out_virtual                      -1.
% 2.06/0.99  --symbol_type_check                     false
% 2.06/0.99  --clausify_out                          false
% 2.06/0.99  --sig_cnt_out                           false
% 2.06/0.99  --trig_cnt_out                          false
% 2.06/0.99  --trig_cnt_out_tolerance                1.
% 2.06/0.99  --trig_cnt_out_sk_spl                   false
% 2.06/0.99  --abstr_cl_out                          false
% 2.06/0.99  
% 2.06/0.99  ------ Global Options
% 2.06/0.99  
% 2.06/0.99  --schedule                              default
% 2.06/0.99  --add_important_lit                     false
% 2.06/0.99  --prop_solver_per_cl                    1000
% 2.06/0.99  --min_unsat_core                        false
% 2.06/0.99  --soft_assumptions                      false
% 2.06/0.99  --soft_lemma_size                       3
% 2.06/0.99  --prop_impl_unit_size                   0
% 2.06/0.99  --prop_impl_unit                        []
% 2.06/0.99  --share_sel_clauses                     true
% 2.06/0.99  --reset_solvers                         false
% 2.06/0.99  --bc_imp_inh                            [conj_cone]
% 2.06/0.99  --conj_cone_tolerance                   3.
% 2.06/0.99  --extra_neg_conj                        none
% 2.06/0.99  --large_theory_mode                     true
% 2.06/0.99  --prolific_symb_bound                   200
% 2.06/0.99  --lt_threshold                          2000
% 2.06/0.99  --clause_weak_htbl                      true
% 2.06/0.99  --gc_record_bc_elim                     false
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing Options
% 2.06/0.99  
% 2.06/0.99  --preprocessing_flag                    true
% 2.06/0.99  --time_out_prep_mult                    0.1
% 2.06/0.99  --splitting_mode                        input
% 2.06/0.99  --splitting_grd                         true
% 2.06/0.99  --splitting_cvd                         false
% 2.06/0.99  --splitting_cvd_svl                     false
% 2.06/0.99  --splitting_nvd                         32
% 2.06/0.99  --sub_typing                            true
% 2.06/0.99  --prep_gs_sim                           true
% 2.06/0.99  --prep_unflatten                        true
% 2.06/0.99  --prep_res_sim                          true
% 2.06/0.99  --prep_upred                            true
% 2.06/0.99  --prep_sem_filter                       exhaustive
% 2.06/0.99  --prep_sem_filter_out                   false
% 2.06/0.99  --pred_elim                             true
% 2.06/0.99  --res_sim_input                         true
% 2.06/0.99  --eq_ax_congr_red                       true
% 2.06/0.99  --pure_diseq_elim                       true
% 2.06/0.99  --brand_transform                       false
% 2.06/0.99  --non_eq_to_eq                          false
% 2.06/0.99  --prep_def_merge                        true
% 2.06/0.99  --prep_def_merge_prop_impl              false
% 2.06/0.99  --prep_def_merge_mbd                    true
% 2.06/0.99  --prep_def_merge_tr_red                 false
% 2.06/0.99  --prep_def_merge_tr_cl                  false
% 2.06/0.99  --smt_preprocessing                     true
% 2.06/0.99  --smt_ac_axioms                         fast
% 2.06/0.99  --preprocessed_out                      false
% 2.06/0.99  --preprocessed_stats                    false
% 2.06/0.99  
% 2.06/0.99  ------ Abstraction refinement Options
% 2.06/0.99  
% 2.06/0.99  --abstr_ref                             []
% 2.06/0.99  --abstr_ref_prep                        false
% 2.06/0.99  --abstr_ref_until_sat                   false
% 2.06/0.99  --abstr_ref_sig_restrict                funpre
% 2.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.06/0.99  --abstr_ref_under                       []
% 2.06/0.99  
% 2.06/0.99  ------ SAT Options
% 2.06/0.99  
% 2.06/0.99  --sat_mode                              false
% 2.06/0.99  --sat_fm_restart_options                ""
% 2.06/0.99  --sat_gr_def                            false
% 2.06/0.99  --sat_epr_types                         true
% 2.06/0.99  --sat_non_cyclic_types                  false
% 2.06/0.99  --sat_finite_models                     false
% 2.06/0.99  --sat_fm_lemmas                         false
% 2.06/0.99  --sat_fm_prep                           false
% 2.06/0.99  --sat_fm_uc_incr                        true
% 2.06/0.99  --sat_out_model                         small
% 2.06/0.99  --sat_out_clauses                       false
% 2.06/0.99  
% 2.06/0.99  ------ QBF Options
% 2.06/0.99  
% 2.06/0.99  --qbf_mode                              false
% 2.06/0.99  --qbf_elim_univ                         false
% 2.06/0.99  --qbf_dom_inst                          none
% 2.06/0.99  --qbf_dom_pre_inst                      false
% 2.06/0.99  --qbf_sk_in                             false
% 2.06/0.99  --qbf_pred_elim                         true
% 2.06/0.99  --qbf_split                             512
% 2.06/0.99  
% 2.06/0.99  ------ BMC1 Options
% 2.06/0.99  
% 2.06/0.99  --bmc1_incremental                      false
% 2.06/0.99  --bmc1_axioms                           reachable_all
% 2.06/0.99  --bmc1_min_bound                        0
% 2.06/0.99  --bmc1_max_bound                        -1
% 2.06/0.99  --bmc1_max_bound_default                -1
% 2.06/0.99  --bmc1_symbol_reachability              true
% 2.06/0.99  --bmc1_property_lemmas                  false
% 2.06/0.99  --bmc1_k_induction                      false
% 2.06/0.99  --bmc1_non_equiv_states                 false
% 2.06/0.99  --bmc1_deadlock                         false
% 2.06/0.99  --bmc1_ucm                              false
% 2.06/0.99  --bmc1_add_unsat_core                   none
% 2.06/0.99  --bmc1_unsat_core_children              false
% 2.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.06/0.99  --bmc1_out_stat                         full
% 2.06/0.99  --bmc1_ground_init                      false
% 2.06/0.99  --bmc1_pre_inst_next_state              false
% 2.06/0.99  --bmc1_pre_inst_state                   false
% 2.06/0.99  --bmc1_pre_inst_reach_state             false
% 2.06/0.99  --bmc1_out_unsat_core                   false
% 2.06/0.99  --bmc1_aig_witness_out                  false
% 2.06/0.99  --bmc1_verbose                          false
% 2.06/0.99  --bmc1_dump_clauses_tptp                false
% 2.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.06/0.99  --bmc1_dump_file                        -
% 2.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.06/0.99  --bmc1_ucm_extend_mode                  1
% 2.06/0.99  --bmc1_ucm_init_mode                    2
% 2.06/0.99  --bmc1_ucm_cone_mode                    none
% 2.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.06/0.99  --bmc1_ucm_relax_model                  4
% 2.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.06/0.99  --bmc1_ucm_layered_model                none
% 2.06/0.99  --bmc1_ucm_max_lemma_size               10
% 2.06/0.99  
% 2.06/0.99  ------ AIG Options
% 2.06/0.99  
% 2.06/0.99  --aig_mode                              false
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation Options
% 2.06/0.99  
% 2.06/0.99  --instantiation_flag                    true
% 2.06/0.99  --inst_sos_flag                         false
% 2.06/0.99  --inst_sos_phase                        true
% 2.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.06/0.99  --inst_lit_sel_side                     none
% 2.06/0.99  --inst_solver_per_active                1400
% 2.06/0.99  --inst_solver_calls_frac                1.
% 2.06/0.99  --inst_passive_queue_type               priority_queues
% 2.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.06/0.99  --inst_passive_queues_freq              [25;2]
% 2.06/0.99  --inst_dismatching                      true
% 2.06/0.99  --inst_eager_unprocessed_to_passive     true
% 2.06/0.99  --inst_prop_sim_given                   true
% 2.06/0.99  --inst_prop_sim_new                     false
% 2.06/0.99  --inst_subs_new                         false
% 2.06/0.99  --inst_eq_res_simp                      false
% 2.06/0.99  --inst_subs_given                       false
% 2.06/0.99  --inst_orphan_elimination               true
% 2.06/0.99  --inst_learning_loop_flag               true
% 2.06/0.99  --inst_learning_start                   3000
% 2.06/0.99  --inst_learning_factor                  2
% 2.06/0.99  --inst_start_prop_sim_after_learn       3
% 2.06/0.99  --inst_sel_renew                        solver
% 2.06/0.99  --inst_lit_activity_flag                true
% 2.06/0.99  --inst_restr_to_given                   false
% 2.06/0.99  --inst_activity_threshold               500
% 2.06/0.99  --inst_out_proof                        true
% 2.06/0.99  
% 2.06/0.99  ------ Resolution Options
% 2.06/0.99  
% 2.06/0.99  --resolution_flag                       false
% 2.06/0.99  --res_lit_sel                           adaptive
% 2.06/0.99  --res_lit_sel_side                      none
% 2.06/0.99  --res_ordering                          kbo
% 2.06/0.99  --res_to_prop_solver                    active
% 2.06/0.99  --res_prop_simpl_new                    false
% 2.06/0.99  --res_prop_simpl_given                  true
% 2.06/0.99  --res_passive_queue_type                priority_queues
% 2.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.06/0.99  --res_passive_queues_freq               [15;5]
% 2.06/0.99  --res_forward_subs                      full
% 2.06/0.99  --res_backward_subs                     full
% 2.06/0.99  --res_forward_subs_resolution           true
% 2.06/0.99  --res_backward_subs_resolution          true
% 2.06/0.99  --res_orphan_elimination                true
% 2.06/0.99  --res_time_limit                        2.
% 2.06/0.99  --res_out_proof                         true
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Options
% 2.06/0.99  
% 2.06/0.99  --superposition_flag                    true
% 2.06/0.99  --sup_passive_queue_type                priority_queues
% 2.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.06/0.99  --demod_completeness_check              fast
% 2.06/0.99  --demod_use_ground                      true
% 2.06/0.99  --sup_to_prop_solver                    passive
% 2.06/0.99  --sup_prop_simpl_new                    true
% 2.06/0.99  --sup_prop_simpl_given                  true
% 2.06/0.99  --sup_fun_splitting                     false
% 2.06/0.99  --sup_smt_interval                      50000
% 2.06/0.99  
% 2.06/0.99  ------ Superposition Simplification Setup
% 2.06/0.99  
% 2.06/0.99  --sup_indices_passive                   []
% 2.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_full_bw                           [BwDemod]
% 2.06/0.99  --sup_immed_triv                        [TrivRules]
% 2.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_immed_bw_main                     []
% 2.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.06/0.99  
% 2.06/0.99  ------ Combination Options
% 2.06/0.99  
% 2.06/0.99  --comb_res_mult                         3
% 2.06/0.99  --comb_sup_mult                         2
% 2.06/0.99  --comb_inst_mult                        10
% 2.06/0.99  
% 2.06/0.99  ------ Debug Options
% 2.06/0.99  
% 2.06/0.99  --dbg_backtrace                         false
% 2.06/0.99  --dbg_dump_prop_clauses                 false
% 2.06/0.99  --dbg_dump_prop_clauses_file            -
% 2.06/0.99  --dbg_out_stat                          false
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  ------ Proving...
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS status Theorem for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  fof(f9,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f30,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f9])).
% 2.06/0.99  
% 2.06/0.99  fof(f68,plain,(
% 2.06/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f30])).
% 2.06/0.99  
% 2.06/0.99  fof(f13,axiom,(
% 2.06/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f37,plain,(
% 2.06/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f13])).
% 2.06/0.99  
% 2.06/0.99  fof(f52,plain,(
% 2.06/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.99    inference(nnf_transformation,[],[f37])).
% 2.06/0.99  
% 2.06/0.99  fof(f76,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f52])).
% 2.06/0.99  
% 2.06/0.99  fof(f1,axiom,(
% 2.06/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f23,plain,(
% 2.06/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f1])).
% 2.06/0.99  
% 2.06/0.99  fof(f59,plain,(
% 2.06/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f23])).
% 2.06/0.99  
% 2.06/0.99  fof(f18,axiom,(
% 2.06/0.99    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f46,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f18])).
% 2.06/0.99  
% 2.06/0.99  fof(f47,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.06/0.99    inference(flattening,[],[f46])).
% 2.06/0.99  
% 2.06/0.99  fof(f84,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f47])).
% 2.06/0.99  
% 2.06/0.99  fof(f16,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0))))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f42,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f16])).
% 2.06/0.99  
% 2.06/0.99  fof(f43,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) <=> v1_tex_2(X1,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(flattening,[],[f42])).
% 2.06/0.99  
% 2.06/0.99  fof(f53,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (! [X2] : (((v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) & (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f43])).
% 2.06/0.99  
% 2.06/0.99  fof(f81,plain,(
% 2.06/0.99    ( ! [X2,X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f53])).
% 2.06/0.99  
% 2.06/0.99  fof(f92,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(equality_resolution,[],[f81])).
% 2.06/0.99  
% 2.06/0.99  fof(f19,conjecture,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f20,negated_conjecture,(
% 2.06/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.06/0.99    inference(negated_conjecture,[],[f19])).
% 2.06/0.99  
% 2.06/0.99  fof(f48,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f20])).
% 2.06/0.99  
% 2.06/0.99  fof(f49,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f48])).
% 2.06/0.99  
% 2.06/0.99  fof(f54,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(nnf_transformation,[],[f49])).
% 2.06/0.99  
% 2.06/0.99  fof(f55,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f54])).
% 2.06/0.99  
% 2.06/0.99  fof(f57,plain,(
% 2.06/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f56,plain,(
% 2.06/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f58,plain,(
% 2.06/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f55,f57,f56])).
% 2.06/0.99  
% 2.06/0.99  fof(f89,plain,(
% 2.06/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f58])).
% 2.06/0.99  
% 2.06/0.99  fof(f86,plain,(
% 2.06/0.99    l1_pre_topc(sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f58])).
% 2.06/0.99  
% 2.06/0.99  fof(f85,plain,(
% 2.06/0.99    ~v2_struct_0(sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f58])).
% 2.06/0.99  
% 2.06/0.99  fof(f14,axiom,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f21,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.06/0.99  
% 2.06/0.99  fof(f38,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f21])).
% 2.06/0.99  
% 2.06/0.99  fof(f39,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f38])).
% 2.06/0.99  
% 2.06/0.99  fof(f78,plain,(
% 2.06/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f39])).
% 2.06/0.99  
% 2.06/0.99  fof(f87,plain,(
% 2.06/0.99    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.06/0.99    inference(cnf_transformation,[],[f58])).
% 2.06/0.99  
% 2.06/0.99  fof(f4,axiom,(
% 2.06/0.99    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f50,plain,(
% 2.06/0.99    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 2.06/0.99    introduced(choice_axiom,[])).
% 2.06/0.99  
% 2.06/0.99  fof(f51,plain,(
% 2.06/0.99    ! [X0] : (~v1_subset_1(sK0(X0),X0) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 2.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f50])).
% 2.06/0.99  
% 2.06/0.99  fof(f62,plain,(
% 2.06/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 2.06/0.99    inference(cnf_transformation,[],[f51])).
% 2.06/0.99  
% 2.06/0.99  fof(f63,plain,(
% 2.06/0.99    ( ! [X0] : (~v1_subset_1(sK0(X0),X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f51])).
% 2.06/0.99  
% 2.06/0.99  fof(f5,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f24,plain,(
% 2.06/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f5])).
% 2.06/0.99  
% 2.06/0.99  fof(f64,plain,(
% 2.06/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f24])).
% 2.06/0.99  
% 2.06/0.99  fof(f12,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f35,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f12])).
% 2.06/0.99  
% 2.06/0.99  fof(f36,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f35])).
% 2.06/0.99  
% 2.06/0.99  fof(f74,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_subset_1(X1,u1_struct_0(X0)) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f36])).
% 2.06/0.99  
% 2.06/0.99  fof(f7,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f26,plain,(
% 2.06/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f7])).
% 2.06/0.99  
% 2.06/0.99  fof(f27,plain,(
% 2.06/0.99    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f26])).
% 2.06/0.99  
% 2.06/0.99  fof(f66,plain,(
% 2.06/0.99    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f27])).
% 2.06/0.99  
% 2.06/0.99  fof(f3,axiom,(
% 2.06/0.99    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f61,plain,(
% 2.06/0.99    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f3])).
% 2.06/0.99  
% 2.06/0.99  fof(f2,axiom,(
% 2.06/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f60,plain,(
% 2.06/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.06/0.99    inference(cnf_transformation,[],[f2])).
% 2.06/0.99  
% 2.06/0.99  fof(f8,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f28,plain,(
% 2.06/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f8])).
% 2.06/0.99  
% 2.06/0.99  fof(f29,plain,(
% 2.06/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f28])).
% 2.06/0.99  
% 2.06/0.99  fof(f67,plain,(
% 2.06/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f29])).
% 2.06/0.99  
% 2.06/0.99  fof(f11,axiom,(
% 2.06/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((~v1_subset_1(X1,u1_struct_0(X0)) & ~v1_xboole_0(X1)) => (v1_zfmisc_1(X1) & ~v1_xboole_0(X1)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f33,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) | (v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f11])).
% 2.06/0.99  
% 2.06/0.99  fof(f34,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) | v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f33])).
% 2.06/0.99  
% 2.06/0.99  fof(f72,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X1) | v1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f34])).
% 2.06/0.99  
% 2.06/0.99  fof(f10,axiom,(
% 2.06/0.99    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f31,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f10])).
% 2.06/0.99  
% 2.06/0.99  fof(f32,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f31])).
% 2.06/0.99  
% 2.06/0.99  fof(f70,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f32])).
% 2.06/0.99  
% 2.06/0.99  fof(f88,plain,(
% 2.06/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 2.06/0.99    inference(cnf_transformation,[],[f58])).
% 2.06/0.99  
% 2.06/0.99  fof(f77,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f39])).
% 2.06/0.99  
% 2.06/0.99  fof(f17,axiom,(
% 2.06/0.99    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f44,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f17])).
% 2.06/0.99  
% 2.06/0.99  fof(f45,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 2.06/0.99    inference(flattening,[],[f44])).
% 2.06/0.99  
% 2.06/0.99  fof(f83,plain,(
% 2.06/0.99    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f45])).
% 2.06/0.99  
% 2.06/0.99  fof(f6,axiom,(
% 2.06/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f25,plain,(
% 2.06/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.06/0.99    inference(ennf_transformation,[],[f6])).
% 2.06/0.99  
% 2.06/0.99  fof(f65,plain,(
% 2.06/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f25])).
% 2.06/0.99  
% 2.06/0.99  fof(f15,axiom,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.06/0.99  
% 2.06/0.99  fof(f22,plain,(
% 2.06/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.06/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.06/0.99  
% 2.06/0.99  fof(f40,plain,(
% 2.06/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.06/0.99    inference(ennf_transformation,[],[f22])).
% 2.06/0.99  
% 2.06/0.99  fof(f41,plain,(
% 2.06/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.06/0.99    inference(flattening,[],[f40])).
% 2.06/0.99  
% 2.06/0.99  fof(f80,plain,(
% 2.06/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.06/0.99    inference(cnf_transformation,[],[f41])).
% 2.06/0.99  
% 2.06/0.99  cnf(c_9,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4044,plain,
% 2.06/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 2.06/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 2.06/0.99      | l1_pre_topc(X1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_16,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.06/0.99      | v1_subset_1(X0,X1)
% 2.06/0.99      | X0 = X1 ),
% 2.06/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4043,plain,
% 2.06/0.99      ( X0 = X1
% 2.06/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.06/0.99      | v1_subset_1(X0,X1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4491,plain,
% 2.06/0.99      ( u1_struct_0(X0) = u1_struct_0(X1)
% 2.06/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4044,c_4043]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_0,plain,
% 2.06/0.99      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_25,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,X1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.06/0.99      | v1_xboole_0(X1)
% 2.06/0.99      | v1_zfmisc_1(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_918,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,X1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.06/0.99      | v1_zfmisc_1(X2)
% 2.06/0.99      | v1_zfmisc_1(X1)
% 2.06/0.99      | X1 != X2 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_25]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_919,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,X1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.06/0.99      | v1_zfmisc_1(X1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_918]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4026,plain,
% 2.06/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(X1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_919]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_23,plain,
% 2.06/0.99      ( v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_168,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | v1_tex_2(X0,X1)
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_23,c_9]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_169,plain,
% 2.06/0.99      ( v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_168]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_26,negated_conjecture,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f89]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_236,plain,
% 2.06/0.99      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(prop_impl,[status(thm)],[c_26]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_639,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | k1_tex_2(sK1,sK2) != X0
% 2.06/0.99      | sK1 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_169,c_236]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_640,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_639]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_29,negated_conjecture,
% 2.06/0.99      ( l1_pre_topc(sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_642,plain,
% 2.06/0.99      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_640,c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_643,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_642]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4029,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_30,negated_conjecture,
% 2.06/0.99      ( ~ v2_struct_0(sK1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_31,plain,
% 2.06/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_32,plain,
% 2.06/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_641,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_18,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.06/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_28,negated_conjecture,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1875,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | sK2 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1876,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(X0,sK2),X0)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_1875]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1877,plain,
% 2.06/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | m1_pre_topc(k1_tex_2(X0,sK2),X0) = iProver_top
% 2.06/0.99      | v2_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1876]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1879,plain,
% 2.06/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.06/0.99      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1877]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3415,plain,
% 2.06/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 2.06/0.99      theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3426,plain,
% 2.06/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3415]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3407,plain,( X0 = X0 ),theory(equality) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3432,plain,
% 2.06/0.99      ( sK1 = sK1 ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_3407]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5192,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_4029,c_31,c_32,c_641,c_1879,c_3426,c_3432]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5198,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4026,c_5192]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_33,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5299,plain,
% 2.06/0.99      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5198,c_33]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5536,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4491,c_5299]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5839,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5536,c_31,c_32,c_1879,c_3426,c_3432]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4,plain,
% 2.06/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4046,plain,
% 2.06/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4409,plain,
% 2.06/0.99      ( sK0(X0) = X0 | v1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_4046,c_4043]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_3,plain,
% 2.06/0.99      ( ~ v1_subset_1(sK0(X0),X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_90,plain,
% 2.06/0.99      ( v1_subset_1(sK0(X0),X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5072,plain,
% 2.06/0.99      ( sK0(X0) = X0 ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_4409,c_90]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5077,plain,
% 2.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.06/0.99      inference(demodulation,[status(thm)],[c_5072,c_4046]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5,plain,
% 2.06/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_14,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_struct_0(X1)
% 2.06/0.99      | v1_xboole_0(X0)
% 2.06/0.99      | ~ v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_437,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X2)
% 2.06/0.99      | v1_xboole_0(X0)
% 2.06/0.99      | ~ v1_zfmisc_1(X0)
% 2.06/0.99      | X1 != X2 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_438,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | v1_xboole_0(X0)
% 2.06/0.99      | ~ v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4031,plain,
% 2.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1)) = iProver_top
% 2.06/0.99      | v7_struct_0(X1) = iProver_top
% 2.06/0.99      | v2_struct_0(X1) = iProver_top
% 2.06/0.99      | l1_pre_topc(X1) != iProver_top
% 2.06/0.99      | v1_xboole_0(X0) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6231,plain,
% 2.06/0.99      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v7_struct_0(X0) = iProver_top
% 2.06/0.99      | v2_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5077,c_4031]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_7,plain,
% 2.06/0.99      ( ~ v2_struct_0(X0)
% 2.06/0.99      | ~ l1_struct_0(X0)
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_401,plain,
% 2.06/0.99      ( ~ v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) ),
% 2.06/0.99      inference(resolution,[status(thm)],[c_5,c_7]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_402,plain,
% 2.06/0.99      ( v2_struct_0(X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6486,plain,
% 2.06/0.99      ( v7_struct_0(X0) = iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6231,c_402]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6487,plain,
% 2.06/0.99      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v7_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_6486]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_2,plain,
% 2.06/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4048,plain,
% 2.06/0.99      ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1,plain,
% 2.06/0.99      ( k2_subset_1(X0) = X0 ),
% 2.06/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4062,plain,
% 2.06/0.99      ( v1_subset_1(X0,X0) != iProver_top ),
% 2.06/0.99      inference(light_normalisation,[status(thm)],[c_4048,c_1]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6497,plain,
% 2.06/0.99      ( v7_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(forward_subsumption_resolution,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6487,c_4062]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6503,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1)
% 2.06/0.99      | v7_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5839,c_6497]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_8,plain,
% 2.06/0.99      ( v2_struct_0(X0)
% 2.06/0.99      | ~ l1_struct_0(X0)
% 2.06/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_79,plain,
% 2.06/0.99      ( v2_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_struct_0(X0) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_81,plain,
% 2.06/0.99      ( v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_struct_0(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_79]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_84,plain,
% 2.06/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_86,plain,
% 2.06/0.99      ( l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | l1_struct_0(sK1) = iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_84]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_12,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_struct_0(X1)
% 2.06/0.99      | v1_xboole_0(X0)
% 2.06/0.99      | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_189,plain,
% 2.06/0.99      ( ~ l1_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_12,c_0]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_190,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_struct_0(X1)
% 2.06/0.99      | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_189]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_413,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X2)
% 2.06/0.99      | v1_zfmisc_1(X0)
% 2.06/0.99      | X1 != X2 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_190]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_414,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | v1_zfmisc_1(X0) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_413]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4032,plain,
% 2.06/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 2.06/0.99      | v1_subset_1(X0,u1_struct_0(X1)) = iProver_top
% 2.06/0.99      | v7_struct_0(X1) != iProver_top
% 2.06/0.99      | v2_struct_0(X1) = iProver_top
% 2.06/0.99      | l1_pre_topc(X1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(X0) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_414]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5905,plain,
% 2.06/0.99      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v7_struct_0(X0) != iProver_top
% 2.06/0.99      | v2_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5077,c_4032]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_905,plain,
% 2.06/0.99      ( ~ v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | v1_zfmisc_1(X1)
% 2.06/0.99      | u1_struct_0(X0) != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_401]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_906,plain,
% 2.06/0.99      ( ~ v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_905]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_907,plain,
% 2.06/0.99      ( v2_struct_0(X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_906]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5980,plain,
% 2.06/0.99      ( v7_struct_0(X0) != iProver_top
% 2.06/0.99      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5905,c_907]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5981,plain,
% 2.06/0.99      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top
% 2.06/0.99      | v7_struct_0(X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_5980]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5990,plain,
% 2.06/0.99      ( v7_struct_0(X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 2.06/0.99      inference(forward_subsumption_resolution,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5981,c_4062]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_10,plain,
% 2.06/0.99      ( ~ v1_tex_2(X0,X1)
% 2.06/0.99      | ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_27,negated_conjecture,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_238,plain,
% 2.06/0.99      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) ),
% 2.06/0.99      inference(prop_impl,[status(thm)],[c_27]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_673,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v7_struct_0(X1)
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1)
% 2.06/0.99      | k1_tex_2(sK1,sK2) != X0
% 2.06/0.99      | sK1 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_238]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_674,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v7_struct_0(sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2))
% 2.06/0.99      | v2_struct_0(sK1)
% 2.06/0.99      | ~ l1_pre_topc(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_673]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_676,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 2.06/0.99      | ~ v7_struct_0(sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_674,c_30,c_29]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4027,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_678,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_19,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1911,plain,
% 2.06/0.99      ( v2_struct_0(X0)
% 2.06/0.99      | ~ v2_struct_0(k1_tex_2(X0,X1))
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | sK2 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1912,plain,
% 2.06/0.99      ( v2_struct_0(X0)
% 2.06/0.99      | ~ v2_struct_0(k1_tex_2(X0,sK2))
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_1911]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1913,plain,
% 2.06/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | v2_struct_0(X0) = iProver_top
% 2.06/0.99      | v2_struct_0(k1_tex_2(X0,sK2)) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1912]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1915,plain,
% 2.06/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.06/0.99      | v2_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1913]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5001,plain,
% 2.06/0.99      ( v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_4027,c_31,c_32,c_678,c_1879,c_1915,c_3426,c_3432]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5002,plain,
% 2.06/0.99      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top ),
% 2.06/0.99      inference(renaming,[status(thm)],[c_5001]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_24,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,X1)
% 2.06/0.99      | ~ v1_subset_1(k6_domain_1(X1,X0),X1)
% 2.06/0.99      | v1_xboole_0(X1)
% 2.06/0.99      | ~ v1_zfmisc_1(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4038,plain,
% 2.06/0.99      ( m1_subset_1(X0,X1) != iProver_top
% 2.06/0.99      | v1_subset_1(k6_domain_1(X1,X0),X1) != iProver_top
% 2.06/0.99      | v1_xboole_0(X1) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(X1) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5007,plain,
% 2.06/0.99      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.06/0.99      | v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5002,c_4038]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5184,plain,
% 2.06/0.99      ( v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_5007,c_31,c_32,c_33,c_81,c_86]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_5994,plain,
% 2.06/0.99      ( v7_struct_0(sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_5990,c_5184]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6499,plain,
% 2.06/0.99      ( v7_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top
% 2.06/0.99      | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_6497]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6522,plain,
% 2.06/0.99      ( u1_struct_0(k1_tex_2(sK1,sK2)) = u1_struct_0(sK1) ),
% 2.06/0.99      inference(global_propositional_subsumption,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6503,c_31,c_32,c_81,c_86,c_5839,c_5994,c_6499]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6548,plain,
% 2.06/0.99      ( v7_struct_0(k1_tex_2(sK1,sK2)) != iProver_top
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2)) != iProver_top
% 2.06/0.99      | v1_zfmisc_1(u1_struct_0(sK1)) = iProver_top ),
% 2.06/0.99      inference(superposition,[status(thm)],[c_6522,c_5990]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_6,plain,
% 2.06/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.06/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4455,plain,
% 2.06/0.99      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2)) ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4456,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_4455]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_4458,plain,
% 2.06/0.99      ( m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 2.06/0.99      | l1_pre_topc(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_4456]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_20,plain,
% 2.06/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.06/0.99      | v7_struct_0(k1_tex_2(X1,X0))
% 2.06/0.99      | v2_struct_0(X1)
% 2.06/0.99      | ~ l1_pre_topc(X1) ),
% 2.06/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1893,plain,
% 2.06/0.99      ( v7_struct_0(k1_tex_2(X0,X1))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | sK2 != X1 ),
% 2.06/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1894,plain,
% 2.06/0.99      ( v7_struct_0(k1_tex_2(X0,sK2))
% 2.06/0.99      | v2_struct_0(X0)
% 2.06/0.99      | ~ l1_pre_topc(X0)
% 2.06/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 2.06/0.99      inference(unflattening,[status(thm)],[c_1893]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1895,plain,
% 2.06/0.99      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 2.06/0.99      | v7_struct_0(k1_tex_2(X0,sK2)) = iProver_top
% 2.06/0.99      | v2_struct_0(X0) = iProver_top
% 2.06/0.99      | l1_pre_topc(X0) != iProver_top ),
% 2.06/0.99      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(c_1897,plain,
% 2.06/0.99      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 2.06/0.99      | v7_struct_0(k1_tex_2(sK1,sK2)) = iProver_top
% 2.06/0.99      | v2_struct_0(sK1) = iProver_top
% 2.06/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 2.06/0.99      inference(instantiation,[status(thm)],[c_1895]) ).
% 2.06/0.99  
% 2.06/0.99  cnf(contradiction,plain,
% 2.06/0.99      ( $false ),
% 2.06/0.99      inference(minisat,
% 2.06/0.99                [status(thm)],
% 2.06/0.99                [c_6548,c_6499,c_5994,c_4458,c_3432,c_3426,c_1897,c_1879,
% 2.06/0.99                 c_86,c_81,c_32,c_31]) ).
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.06/0.99  
% 2.06/0.99  ------                               Statistics
% 2.06/0.99  
% 2.06/0.99  ------ General
% 2.06/0.99  
% 2.06/0.99  abstr_ref_over_cycles:                  0
% 2.06/0.99  abstr_ref_under_cycles:                 0
% 2.06/0.99  gc_basic_clause_elim:                   0
% 2.06/0.99  forced_gc_time:                         0
% 2.06/0.99  parsing_time:                           0.01
% 2.06/0.99  unif_index_cands_time:                  0.
% 2.06/0.99  unif_index_add_time:                    0.
% 2.06/0.99  orderings_time:                         0.
% 2.06/0.99  out_proof_time:                         0.016
% 2.06/0.99  total_time:                             0.262
% 2.06/0.99  num_of_symbols:                         49
% 2.06/0.99  num_of_terms:                           3563
% 2.06/0.99  
% 2.06/0.99  ------ Preprocessing
% 2.06/0.99  
% 2.06/0.99  num_of_splits:                          0
% 2.06/0.99  num_of_split_atoms:                     0
% 2.06/0.99  num_of_reused_defs:                     0
% 2.06/0.99  num_eq_ax_congr_red:                    11
% 2.06/0.99  num_of_sem_filtered_clauses:            1
% 2.06/0.99  num_of_subtypes:                        0
% 2.06/0.99  monotx_restored_types:                  0
% 2.06/0.99  sat_num_of_epr_types:                   0
% 2.06/0.99  sat_num_of_non_cyclic_types:            0
% 2.06/0.99  sat_guarded_non_collapsed_types:        0
% 2.06/0.99  num_pure_diseq_elim:                    0
% 2.06/0.99  simp_replaced_by:                       0
% 2.06/0.99  res_preprocessed:                       129
% 2.06/0.99  prep_upred:                             0
% 2.06/0.99  prep_unflattend:                        128
% 2.06/0.99  smt_new_axioms:                         0
% 2.06/0.99  pred_elim_cands:                        8
% 2.06/0.99  pred_elim:                              2
% 2.06/0.99  pred_elim_cl:                           2
% 2.06/0.99  pred_elim_cycles:                       14
% 2.06/0.99  merged_defs:                            6
% 2.06/0.99  merged_defs_ncl:                        0
% 2.06/0.99  bin_hyper_res:                          7
% 2.06/0.99  prep_cycles:                            4
% 2.06/0.99  pred_elim_time:                         0.061
% 2.06/0.99  splitting_time:                         0.
% 2.06/0.99  sem_filter_time:                        0.
% 2.06/0.99  monotx_time:                            0.001
% 2.06/0.99  subtype_inf_time:                       0.
% 2.06/0.99  
% 2.06/0.99  ------ Problem properties
% 2.06/0.99  
% 2.06/0.99  clauses:                                25
% 2.06/0.99  conjectures:                            3
% 2.06/0.99  epr:                                    4
% 2.06/0.99  horn:                                   16
% 2.06/0.99  ground:                                 6
% 2.06/0.99  unary:                                  7
% 2.06/0.99  binary:                                 2
% 2.06/0.99  lits:                                   74
% 2.06/0.99  lits_eq:                                2
% 2.06/0.99  fd_pure:                                0
% 2.06/0.99  fd_pseudo:                              0
% 2.06/0.99  fd_cond:                                0
% 2.06/0.99  fd_pseudo_cond:                         1
% 2.06/0.99  ac_symbols:                             0
% 2.06/0.99  
% 2.06/0.99  ------ Propositional Solver
% 2.06/0.99  
% 2.06/0.99  prop_solver_calls:                      27
% 2.06/0.99  prop_fast_solver_calls:                 1673
% 2.06/0.99  smt_solver_calls:                       0
% 2.06/0.99  smt_fast_solver_calls:                  0
% 2.06/0.99  prop_num_of_clauses:                    1486
% 2.06/0.99  prop_preprocess_simplified:             5607
% 2.06/0.99  prop_fo_subsumed:                       64
% 2.06/0.99  prop_solver_time:                       0.
% 2.06/0.99  smt_solver_time:                        0.
% 2.06/0.99  smt_fast_solver_time:                   0.
% 2.06/0.99  prop_fast_solver_time:                  0.
% 2.06/0.99  prop_unsat_core_time:                   0.
% 2.06/0.99  
% 2.06/0.99  ------ QBF
% 2.06/0.99  
% 2.06/0.99  qbf_q_res:                              0
% 2.06/0.99  qbf_num_tautologies:                    0
% 2.06/0.99  qbf_prep_cycles:                        0
% 2.06/0.99  
% 2.06/0.99  ------ BMC1
% 2.06/0.99  
% 2.06/0.99  bmc1_current_bound:                     -1
% 2.06/0.99  bmc1_last_solved_bound:                 -1
% 2.06/0.99  bmc1_unsat_core_size:                   -1
% 2.06/0.99  bmc1_unsat_core_parents_size:           -1
% 2.06/0.99  bmc1_merge_next_fun:                    0
% 2.06/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.06/0.99  
% 2.06/0.99  ------ Instantiation
% 2.06/0.99  
% 2.06/0.99  inst_num_of_clauses:                    411
% 2.06/0.99  inst_num_in_passive:                    114
% 2.06/0.99  inst_num_in_active:                     221
% 2.06/0.99  inst_num_in_unprocessed:                76
% 2.06/0.99  inst_num_of_loops:                      240
% 2.06/0.99  inst_num_of_learning_restarts:          0
% 2.06/0.99  inst_num_moves_active_passive:          15
% 2.06/0.99  inst_lit_activity:                      0
% 2.06/0.99  inst_lit_activity_moves:                0
% 2.06/0.99  inst_num_tautologies:                   0
% 2.06/0.99  inst_num_prop_implied:                  0
% 2.06/0.99  inst_num_existing_simplified:           0
% 2.06/0.99  inst_num_eq_res_simplified:             0
% 2.06/0.99  inst_num_child_elim:                    0
% 2.06/0.99  inst_num_of_dismatching_blockings:      141
% 2.06/0.99  inst_num_of_non_proper_insts:           412
% 2.06/0.99  inst_num_of_duplicates:                 0
% 2.06/0.99  inst_inst_num_from_inst_to_res:         0
% 2.06/0.99  inst_dismatching_checking_time:         0.
% 2.06/0.99  
% 2.06/0.99  ------ Resolution
% 2.06/0.99  
% 2.06/0.99  res_num_of_clauses:                     0
% 2.06/0.99  res_num_in_passive:                     0
% 2.06/0.99  res_num_in_active:                      0
% 2.06/0.99  res_num_of_loops:                       133
% 2.06/0.99  res_forward_subset_subsumed:            26
% 2.06/0.99  res_backward_subset_subsumed:           2
% 2.06/0.99  res_forward_subsumed:                   1
% 2.06/0.99  res_backward_subsumed:                  1
% 2.06/0.99  res_forward_subsumption_resolution:     2
% 2.06/0.99  res_backward_subsumption_resolution:    0
% 2.06/0.99  res_clause_to_clause_subsumption:       329
% 2.06/0.99  res_orphan_elimination:                 0
% 2.06/0.99  res_tautology_del:                      58
% 2.06/0.99  res_num_eq_res_simplified:              0
% 2.06/0.99  res_num_sel_changes:                    0
% 2.06/0.99  res_moves_from_active_to_pass:          0
% 2.06/0.99  
% 2.06/0.99  ------ Superposition
% 2.06/0.99  
% 2.06/0.99  sup_time_total:                         0.
% 2.06/0.99  sup_time_generating:                    0.
% 2.06/0.99  sup_time_sim_full:                      0.
% 2.06/0.99  sup_time_sim_immed:                     0.
% 2.06/0.99  
% 2.06/0.99  sup_num_of_clauses:                     45
% 2.06/0.99  sup_num_in_active:                      38
% 2.06/0.99  sup_num_in_passive:                     7
% 2.06/0.99  sup_num_of_loops:                       47
% 2.06/0.99  sup_fw_superposition:                   26
% 2.06/0.99  sup_bw_superposition:                   39
% 2.06/0.99  sup_immediate_simplified:               14
% 2.06/0.99  sup_given_eliminated:                   0
% 2.06/0.99  comparisons_done:                       0
% 2.06/0.99  comparisons_avoided:                    0
% 2.06/0.99  
% 2.06/0.99  ------ Simplifications
% 2.06/0.99  
% 2.06/0.99  
% 2.06/0.99  sim_fw_subset_subsumed:                 13
% 2.06/0.99  sim_bw_subset_subsumed:                 4
% 2.06/0.99  sim_fw_subsumed:                        5
% 2.06/0.99  sim_bw_subsumed:                        0
% 2.06/0.99  sim_fw_subsumption_res:                 3
% 2.06/0.99  sim_bw_subsumption_res:                 0
% 2.06/0.99  sim_tautology_del:                      8
% 2.06/0.99  sim_eq_tautology_del:                   2
% 2.06/0.99  sim_eq_res_simp:                        0
% 2.06/0.99  sim_fw_demodulated:                     2
% 2.06/0.99  sim_bw_demodulated:                     7
% 2.06/0.99  sim_light_normalised:                   4
% 2.06/0.99  sim_joinable_taut:                      0
% 2.06/0.99  sim_joinable_simp:                      0
% 2.06/0.99  sim_ac_normalised:                      0
% 2.06/0.99  sim_smt_subsumption:                    0
% 2.06/0.99  
%------------------------------------------------------------------------------
