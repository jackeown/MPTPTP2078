%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:37 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_3816)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK1(X0,X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK3),X0) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | ~ v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2))
            | v1_tex_2(k1_tex_2(sK2,X1),sK2) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).

fof(f84,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f80,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f81,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_18,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2857,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_3550,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2857])).

cnf(c_13,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2861,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3546,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2861])).

cnf(c_4574,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_3546])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2868,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3539,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2859,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_subset_1(X0_46,X1_46)
    | X1_46 = X0_46 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3548,plain,
    ( X0_46 = X1_46
    | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
    | v1_subset_1(X1_46,X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2859])).

cnf(c_3979,plain,
    ( k6_domain_1(X0_46,X1_46) = X0_46
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3539,c_3548])).

cnf(c_23,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2854,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_3553,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2854])).

cnf(c_4903,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3979,c_3553])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( v7_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_87,plain,
    ( v7_struct_0(sK2)
    | ~ v1_zfmisc_1(u1_struct_0(sK2))
    | ~ l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_91,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2930,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_2929,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2857])).

cnf(c_2931,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2929])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v7_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2855,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | v7_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_2936,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | v7_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_4,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_362,plain,
    ( ~ v7_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_1,c_4])).

cnf(c_2848,plain,
    ( ~ v7_struct_0(X0_47)
    | v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_362])).

cnf(c_3782,plain,
    ( ~ v7_struct_0(k1_tex_2(X0_47,X0_46))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46)))
    | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_3784,plain,
    ( ~ v7_struct_0(k1_tex_2(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3782])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2867,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3795,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_2867])).

cnf(c_3797,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3795])).

cnf(c_3796,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3795])).

cnf(c_3798,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3796])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2865,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_zfmisc_1(X1_46)
    | v1_xboole_0(X1_46)
    | k6_domain_1(X1_46,X0_46) != X1_46 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3800,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2865])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2869,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3898,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_3900,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3898])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2870,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_subset_1(X0_46,X1_46)
    | ~ v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3864,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2870])).

cnf(c_3991,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3864])).

cnf(c_3992,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3991])).

cnf(c_4004,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(X0_46,u1_struct_0(sK2))
    | u1_struct_0(sK2) = X0_46 ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_4107,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4004])).

cnf(c_4110,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4107])).

cnf(c_4109,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,X0_46))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4107])).

cnf(c_4111,plain,
    ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4109])).

cnf(c_24,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2853,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_3554,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2853])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_390,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_1])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_2846,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v7_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_391])).

cnf(c_3561,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_4809,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3554,c_3561])).

cnf(c_7,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_215,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_1495,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_215])).

cnf(c_1496,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_1495])).

cnf(c_1498,plain,
    ( ~ v7_struct_0(sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v2_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_27,c_26])).

cnf(c_1499,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ v7_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_1498])).

cnf(c_1500,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1499])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2856,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2932,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2856])).

cnf(c_2934,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2932])).

cnf(c_2946,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_2948,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2946])).

cnf(c_4812,plain,
    ( v7_struct_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4809,c_28,c_29,c_30,c_1500,c_2931,c_2934,c_2948])).

cnf(c_4814,plain,
    ( ~ v7_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4812])).

cnf(c_2881,plain,
    ( ~ v1_zfmisc_1(X0_46)
    | v1_zfmisc_1(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_4213,plain,
    ( v1_zfmisc_1(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
    | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
    inference(instantiation,[status(thm)],[c_2881])).

cnf(c_4934,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
    | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4213])).

cnf(c_4937,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_5125,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4903,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3900,c_3991,c_3992,c_4110,c_4111,c_4814,c_4937])).

cnf(c_5508,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4574,c_5125])).

cnf(c_3813,plain,
    ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ l1_pre_topc(X0_47)
    | sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_3815,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3813])).

cnf(c_4925,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4903])).

cnf(c_5916,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5508,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3816,c_3900,c_3991,c_3992,c_4110,c_4111,c_4814,c_4903,c_4937])).

cnf(c_14,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2860,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3547,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_4884,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3547,c_3548])).

cnf(c_12,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2862,plain,
    ( v1_tex_2(X0_47,X1_47)
    | ~ m1_pre_topc(X0_47,X1_47)
    | ~ v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3545,plain,
    ( v1_tex_2(X0_47,X1_47) = iProver_top
    | m1_pre_topc(X0_47,X1_47) != iProver_top
    | v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47)) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_5786,plain,
    ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
    | v1_tex_2(X1_47,X0_47) = iProver_top
    | m1_pre_topc(X1_47,X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4884,c_3545])).

cnf(c_5788,plain,
    ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
    | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_3550,c_5786])).

cnf(c_5798,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5788,c_5125])).

cnf(c_5790,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5788])).

cnf(c_5892,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5798,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3900,c_3991,c_3992,c_4110,c_4111,c_4814,c_4903,c_4937,c_5790])).

cnf(c_5918,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5916,c_5892])).

cnf(c_2874,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_4010,plain,
    ( X0_46 != X1_46
    | u1_struct_0(sK2) != X1_46
    | u1_struct_0(sK2) = X0_46 ),
    inference(instantiation,[status(thm)],[c_2874])).

cnf(c_4124,plain,
    ( X0_46 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0_46
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4010])).

cnf(c_4429,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(X0_47)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4124])).

cnf(c_4708,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4429])).

cnf(c_2873,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_2901,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2873])).

cnf(c_2880,plain,
    ( X0_47 != X1_47
    | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
    theory(equality)).

cnf(c_2892,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2880])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5918,c_4937,c_4814,c_4708,c_3900,c_3784,c_2936,c_2930,c_2901,c_2892,c_91,c_87,c_25,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n005.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:30:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.32/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.00  
% 2.32/1.00  ------  iProver source info
% 2.32/1.00  
% 2.32/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.00  git: non_committed_changes: false
% 2.32/1.00  git: last_make_outside_of_git: false
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     num_symb
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       true
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  ------ Parsing...
% 2.32/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.32/1.00  ------ Proving...
% 2.32/1.00  ------ Problem Properties 
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  clauses                                 25
% 2.32/1.00  conjectures                             5
% 2.32/1.00  EPR                                     4
% 2.32/1.00  Horn                                    14
% 2.32/1.00  unary                                   3
% 2.32/1.00  binary                                  3
% 2.32/1.00  lits                                    79
% 2.32/1.00  lits eq                                 4
% 2.32/1.00  fd_pure                                 0
% 2.32/1.00  fd_pseudo                               0
% 2.32/1.00  fd_cond                                 0
% 2.32/1.00  fd_pseudo_cond                          1
% 2.32/1.00  AC symbols                              0
% 2.32/1.00  
% 2.32/1.00  ------ Schedule dynamic 5 is on 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ 
% 2.32/1.00  Current options:
% 2.32/1.00  ------ 
% 2.32/1.00  
% 2.32/1.00  ------ Input Options
% 2.32/1.00  
% 2.32/1.00  --out_options                           all
% 2.32/1.00  --tptp_safe_out                         true
% 2.32/1.00  --problem_path                          ""
% 2.32/1.00  --include_path                          ""
% 2.32/1.00  --clausifier                            res/vclausify_rel
% 2.32/1.00  --clausifier_options                    --mode clausify
% 2.32/1.00  --stdin                                 false
% 2.32/1.00  --stats_out                             all
% 2.32/1.00  
% 2.32/1.00  ------ General Options
% 2.32/1.00  
% 2.32/1.00  --fof                                   false
% 2.32/1.00  --time_out_real                         305.
% 2.32/1.00  --time_out_virtual                      -1.
% 2.32/1.00  --symbol_type_check                     false
% 2.32/1.00  --clausify_out                          false
% 2.32/1.00  --sig_cnt_out                           false
% 2.32/1.00  --trig_cnt_out                          false
% 2.32/1.00  --trig_cnt_out_tolerance                1.
% 2.32/1.00  --trig_cnt_out_sk_spl                   false
% 2.32/1.00  --abstr_cl_out                          false
% 2.32/1.00  
% 2.32/1.00  ------ Global Options
% 2.32/1.00  
% 2.32/1.00  --schedule                              default
% 2.32/1.00  --add_important_lit                     false
% 2.32/1.00  --prop_solver_per_cl                    1000
% 2.32/1.00  --min_unsat_core                        false
% 2.32/1.00  --soft_assumptions                      false
% 2.32/1.00  --soft_lemma_size                       3
% 2.32/1.00  --prop_impl_unit_size                   0
% 2.32/1.00  --prop_impl_unit                        []
% 2.32/1.00  --share_sel_clauses                     true
% 2.32/1.00  --reset_solvers                         false
% 2.32/1.00  --bc_imp_inh                            [conj_cone]
% 2.32/1.00  --conj_cone_tolerance                   3.
% 2.32/1.00  --extra_neg_conj                        none
% 2.32/1.00  --large_theory_mode                     true
% 2.32/1.00  --prolific_symb_bound                   200
% 2.32/1.00  --lt_threshold                          2000
% 2.32/1.00  --clause_weak_htbl                      true
% 2.32/1.00  --gc_record_bc_elim                     false
% 2.32/1.00  
% 2.32/1.00  ------ Preprocessing Options
% 2.32/1.00  
% 2.32/1.00  --preprocessing_flag                    true
% 2.32/1.00  --time_out_prep_mult                    0.1
% 2.32/1.00  --splitting_mode                        input
% 2.32/1.00  --splitting_grd                         true
% 2.32/1.00  --splitting_cvd                         false
% 2.32/1.00  --splitting_cvd_svl                     false
% 2.32/1.00  --splitting_nvd                         32
% 2.32/1.00  --sub_typing                            true
% 2.32/1.00  --prep_gs_sim                           true
% 2.32/1.00  --prep_unflatten                        true
% 2.32/1.00  --prep_res_sim                          true
% 2.32/1.00  --prep_upred                            true
% 2.32/1.00  --prep_sem_filter                       exhaustive
% 2.32/1.00  --prep_sem_filter_out                   false
% 2.32/1.00  --pred_elim                             true
% 2.32/1.00  --res_sim_input                         true
% 2.32/1.00  --eq_ax_congr_red                       true
% 2.32/1.00  --pure_diseq_elim                       true
% 2.32/1.00  --brand_transform                       false
% 2.32/1.00  --non_eq_to_eq                          false
% 2.32/1.00  --prep_def_merge                        true
% 2.32/1.00  --prep_def_merge_prop_impl              false
% 2.32/1.00  --prep_def_merge_mbd                    true
% 2.32/1.00  --prep_def_merge_tr_red                 false
% 2.32/1.00  --prep_def_merge_tr_cl                  false
% 2.32/1.00  --smt_preprocessing                     true
% 2.32/1.00  --smt_ac_axioms                         fast
% 2.32/1.00  --preprocessed_out                      false
% 2.32/1.00  --preprocessed_stats                    false
% 2.32/1.00  
% 2.32/1.00  ------ Abstraction refinement Options
% 2.32/1.00  
% 2.32/1.00  --abstr_ref                             []
% 2.32/1.00  --abstr_ref_prep                        false
% 2.32/1.00  --abstr_ref_until_sat                   false
% 2.32/1.00  --abstr_ref_sig_restrict                funpre
% 2.32/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.00  --abstr_ref_under                       []
% 2.32/1.00  
% 2.32/1.00  ------ SAT Options
% 2.32/1.00  
% 2.32/1.00  --sat_mode                              false
% 2.32/1.00  --sat_fm_restart_options                ""
% 2.32/1.00  --sat_gr_def                            false
% 2.32/1.00  --sat_epr_types                         true
% 2.32/1.00  --sat_non_cyclic_types                  false
% 2.32/1.00  --sat_finite_models                     false
% 2.32/1.00  --sat_fm_lemmas                         false
% 2.32/1.00  --sat_fm_prep                           false
% 2.32/1.00  --sat_fm_uc_incr                        true
% 2.32/1.00  --sat_out_model                         small
% 2.32/1.00  --sat_out_clauses                       false
% 2.32/1.00  
% 2.32/1.00  ------ QBF Options
% 2.32/1.00  
% 2.32/1.00  --qbf_mode                              false
% 2.32/1.00  --qbf_elim_univ                         false
% 2.32/1.00  --qbf_dom_inst                          none
% 2.32/1.00  --qbf_dom_pre_inst                      false
% 2.32/1.00  --qbf_sk_in                             false
% 2.32/1.00  --qbf_pred_elim                         true
% 2.32/1.00  --qbf_split                             512
% 2.32/1.00  
% 2.32/1.00  ------ BMC1 Options
% 2.32/1.00  
% 2.32/1.00  --bmc1_incremental                      false
% 2.32/1.00  --bmc1_axioms                           reachable_all
% 2.32/1.00  --bmc1_min_bound                        0
% 2.32/1.00  --bmc1_max_bound                        -1
% 2.32/1.00  --bmc1_max_bound_default                -1
% 2.32/1.00  --bmc1_symbol_reachability              true
% 2.32/1.00  --bmc1_property_lemmas                  false
% 2.32/1.00  --bmc1_k_induction                      false
% 2.32/1.00  --bmc1_non_equiv_states                 false
% 2.32/1.00  --bmc1_deadlock                         false
% 2.32/1.00  --bmc1_ucm                              false
% 2.32/1.00  --bmc1_add_unsat_core                   none
% 2.32/1.00  --bmc1_unsat_core_children              false
% 2.32/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.00  --bmc1_out_stat                         full
% 2.32/1.00  --bmc1_ground_init                      false
% 2.32/1.00  --bmc1_pre_inst_next_state              false
% 2.32/1.00  --bmc1_pre_inst_state                   false
% 2.32/1.00  --bmc1_pre_inst_reach_state             false
% 2.32/1.00  --bmc1_out_unsat_core                   false
% 2.32/1.00  --bmc1_aig_witness_out                  false
% 2.32/1.00  --bmc1_verbose                          false
% 2.32/1.00  --bmc1_dump_clauses_tptp                false
% 2.32/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.00  --bmc1_dump_file                        -
% 2.32/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.00  --bmc1_ucm_extend_mode                  1
% 2.32/1.00  --bmc1_ucm_init_mode                    2
% 2.32/1.00  --bmc1_ucm_cone_mode                    none
% 2.32/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.00  --bmc1_ucm_relax_model                  4
% 2.32/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.00  --bmc1_ucm_layered_model                none
% 2.32/1.00  --bmc1_ucm_max_lemma_size               10
% 2.32/1.00  
% 2.32/1.00  ------ AIG Options
% 2.32/1.00  
% 2.32/1.00  --aig_mode                              false
% 2.32/1.00  
% 2.32/1.00  ------ Instantiation Options
% 2.32/1.00  
% 2.32/1.00  --instantiation_flag                    true
% 2.32/1.00  --inst_sos_flag                         false
% 2.32/1.00  --inst_sos_phase                        true
% 2.32/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.00  --inst_lit_sel_side                     none
% 2.32/1.00  --inst_solver_per_active                1400
% 2.32/1.00  --inst_solver_calls_frac                1.
% 2.32/1.00  --inst_passive_queue_type               priority_queues
% 2.32/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.00  --inst_passive_queues_freq              [25;2]
% 2.32/1.00  --inst_dismatching                      true
% 2.32/1.00  --inst_eager_unprocessed_to_passive     true
% 2.32/1.00  --inst_prop_sim_given                   true
% 2.32/1.00  --inst_prop_sim_new                     false
% 2.32/1.00  --inst_subs_new                         false
% 2.32/1.00  --inst_eq_res_simp                      false
% 2.32/1.00  --inst_subs_given                       false
% 2.32/1.00  --inst_orphan_elimination               true
% 2.32/1.00  --inst_learning_loop_flag               true
% 2.32/1.00  --inst_learning_start                   3000
% 2.32/1.00  --inst_learning_factor                  2
% 2.32/1.00  --inst_start_prop_sim_after_learn       3
% 2.32/1.00  --inst_sel_renew                        solver
% 2.32/1.00  --inst_lit_activity_flag                true
% 2.32/1.00  --inst_restr_to_given                   false
% 2.32/1.00  --inst_activity_threshold               500
% 2.32/1.00  --inst_out_proof                        true
% 2.32/1.00  
% 2.32/1.00  ------ Resolution Options
% 2.32/1.00  
% 2.32/1.00  --resolution_flag                       false
% 2.32/1.00  --res_lit_sel                           adaptive
% 2.32/1.00  --res_lit_sel_side                      none
% 2.32/1.00  --res_ordering                          kbo
% 2.32/1.00  --res_to_prop_solver                    active
% 2.32/1.00  --res_prop_simpl_new                    false
% 2.32/1.00  --res_prop_simpl_given                  true
% 2.32/1.00  --res_passive_queue_type                priority_queues
% 2.32/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.00  --res_passive_queues_freq               [15;5]
% 2.32/1.00  --res_forward_subs                      full
% 2.32/1.00  --res_backward_subs                     full
% 2.32/1.00  --res_forward_subs_resolution           true
% 2.32/1.00  --res_backward_subs_resolution          true
% 2.32/1.00  --res_orphan_elimination                true
% 2.32/1.00  --res_time_limit                        2.
% 2.32/1.00  --res_out_proof                         true
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Options
% 2.32/1.00  
% 2.32/1.00  --superposition_flag                    true
% 2.32/1.00  --sup_passive_queue_type                priority_queues
% 2.32/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.00  --demod_completeness_check              fast
% 2.32/1.00  --demod_use_ground                      true
% 2.32/1.00  --sup_to_prop_solver                    passive
% 2.32/1.00  --sup_prop_simpl_new                    true
% 2.32/1.00  --sup_prop_simpl_given                  true
% 2.32/1.00  --sup_fun_splitting                     false
% 2.32/1.00  --sup_smt_interval                      50000
% 2.32/1.00  
% 2.32/1.00  ------ Superposition Simplification Setup
% 2.32/1.00  
% 2.32/1.00  --sup_indices_passive                   []
% 2.32/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_full_bw                           [BwDemod]
% 2.32/1.00  --sup_immed_triv                        [TrivRules]
% 2.32/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_immed_bw_main                     []
% 2.32/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.00  
% 2.32/1.00  ------ Combination Options
% 2.32/1.00  
% 2.32/1.00  --comb_res_mult                         3
% 2.32/1.00  --comb_sup_mult                         2
% 2.32/1.00  --comb_inst_mult                        10
% 2.32/1.00  
% 2.32/1.00  ------ Debug Options
% 2.32/1.00  
% 2.32/1.00  --dbg_backtrace                         false
% 2.32/1.00  --dbg_dump_prop_clauses                 false
% 2.32/1.00  --dbg_dump_prop_clauses_file            -
% 2.32/1.00  --dbg_out_stat                          false
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  ------ Proving...
% 2.32/1.00  
% 2.32/1.00  
% 2.32/1.00  % SZS status Theorem for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.00  
% 2.32/1.00  fof(f12,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f17,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.32/1.00  
% 2.32/1.00  fof(f35,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f17])).
% 2.32/1.00  
% 2.32/1.00  fof(f36,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f35])).
% 2.32/1.00  
% 2.32/1.00  fof(f76,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f36])).
% 2.32/1.00  
% 2.32/1.00  fof(f10,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f32,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f10])).
% 2.32/1.00  
% 2.32/1.00  fof(f33,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(flattening,[],[f32])).
% 2.32/1.00  
% 2.32/1.00  fof(f47,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f33])).
% 2.32/1.00  
% 2.32/1.00  fof(f48,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(rectify,[],[f47])).
% 2.32/1.00  
% 2.32/1.00  fof(f49,plain,(
% 2.32/1.00    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f50,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f48,f49])).
% 2.32/1.00  
% 2.32/1.00  fof(f71,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f50])).
% 2.32/1.00  
% 2.32/1.00  fof(f6,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f26,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f6])).
% 2.32/1.00  
% 2.32/1.00  fof(f27,plain,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.32/1.00    inference(flattening,[],[f26])).
% 2.32/1.00  
% 2.32/1.00  fof(f62,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f27])).
% 2.32/1.00  
% 2.32/1.00  fof(f11,axiom,(
% 2.32/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f34,plain,(
% 2.32/1.00    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f11])).
% 2.32/1.00  
% 2.32/1.00  fof(f51,plain,(
% 2.32/1.00    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/1.00    inference(nnf_transformation,[],[f34])).
% 2.32/1.00  
% 2.32/1.00  fof(f74,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.32/1.00    inference(cnf_transformation,[],[f51])).
% 2.32/1.00  
% 2.32/1.00  fof(f15,conjecture,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f16,negated_conjecture,(
% 2.32/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.32/1.00    inference(negated_conjecture,[],[f15])).
% 2.32/1.00  
% 2.32/1.00  fof(f41,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f16])).
% 2.32/1.00  
% 2.32/1.00  fof(f42,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f41])).
% 2.32/1.00  
% 2.32/1.00  fof(f52,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f42])).
% 2.32/1.00  
% 2.32/1.00  fof(f53,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f52])).
% 2.32/1.00  
% 2.32/1.00  fof(f55,plain,(
% 2.32/1.00    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f54,plain,(
% 2.32/1.00    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f56,plain,(
% 2.32/1.00    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f53,f55,f54])).
% 2.32/1.00  
% 2.32/1.00  fof(f84,plain,(
% 2.32/1.00    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f56])).
% 2.32/1.00  
% 2.32/1.00  fof(f80,plain,(
% 2.32/1.00    ~v2_struct_0(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f56])).
% 2.32/1.00  
% 2.32/1.00  fof(f81,plain,(
% 2.32/1.00    l1_pre_topc(sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f56])).
% 2.32/1.00  
% 2.32/1.00  fof(f82,plain,(
% 2.32/1.00    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.32/1.00    inference(cnf_transformation,[],[f56])).
% 2.32/1.00  
% 2.32/1.00  fof(f4,axiom,(
% 2.32/1.00    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f22,plain,(
% 2.32/1.00    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f4])).
% 2.32/1.00  
% 2.32/1.00  fof(f23,plain,(
% 2.32/1.00    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f22])).
% 2.32/1.00  
% 2.32/1.00  fof(f60,plain,(
% 2.32/1.00    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f23])).
% 2.32/1.00  
% 2.32/1.00  fof(f2,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f20,plain,(
% 2.32/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f2])).
% 2.32/1.00  
% 2.32/1.00  fof(f58,plain,(
% 2.32/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f20])).
% 2.32/1.00  
% 2.32/1.00  fof(f13,axiom,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f18,plain,(
% 2.32/1.00    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.32/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.32/1.00  
% 2.32/1.00  fof(f37,plain,(
% 2.32/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f18])).
% 2.32/1.00  
% 2.32/1.00  fof(f38,plain,(
% 2.32/1.00    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f37])).
% 2.32/1.00  
% 2.32/1.00  fof(f78,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f5,axiom,(
% 2.32/1.00    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f24,plain,(
% 2.32/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f5])).
% 2.32/1.00  
% 2.32/1.00  fof(f25,plain,(
% 2.32/1.00    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f24])).
% 2.32/1.00  
% 2.32/1.00  fof(f61,plain,(
% 2.32/1.00    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f25])).
% 2.32/1.00  
% 2.32/1.00  fof(f7,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f28,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f7])).
% 2.32/1.00  
% 2.32/1.00  fof(f63,plain,(
% 2.32/1.00    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f28])).
% 2.32/1.00  
% 2.32/1.00  fof(f9,axiom,(
% 2.32/1.00    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f31,plain,(
% 2.32/1.00    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f9])).
% 2.32/1.00  
% 2.32/1.00  fof(f43,plain,(
% 2.32/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.32/1.00    inference(nnf_transformation,[],[f31])).
% 2.32/1.00  
% 2.32/1.00  fof(f44,plain,(
% 2.32/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.32/1.00    inference(rectify,[],[f43])).
% 2.32/1.00  
% 2.32/1.00  fof(f45,plain,(
% 2.32/1.00    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.32/1.00    introduced(choice_axiom,[])).
% 2.32/1.00  
% 2.32/1.00  fof(f46,plain,(
% 2.32/1.00    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.32/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).
% 2.32/1.00  
% 2.32/1.00  fof(f68,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f46])).
% 2.32/1.00  
% 2.32/1.00  fof(f3,axiom,(
% 2.32/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f21,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f3])).
% 2.32/1.00  
% 2.32/1.00  fof(f59,plain,(
% 2.32/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f21])).
% 2.32/1.00  
% 2.32/1.00  fof(f1,axiom,(
% 2.32/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f19,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.32/1.00    inference(ennf_transformation,[],[f1])).
% 2.32/1.00  
% 2.32/1.00  fof(f57,plain,(
% 2.32/1.00    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f19])).
% 2.32/1.00  
% 2.32/1.00  fof(f83,plain,(
% 2.32/1.00    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.32/1.00    inference(cnf_transformation,[],[f56])).
% 2.32/1.00  
% 2.32/1.00  fof(f14,axiom,(
% 2.32/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f39,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f14])).
% 2.32/1.00  
% 2.32/1.00  fof(f40,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f39])).
% 2.32/1.00  
% 2.32/1.00  fof(f79,plain,(
% 2.32/1.00    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f40])).
% 2.32/1.00  
% 2.32/1.00  fof(f8,axiom,(
% 2.32/1.00    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 2.32/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.32/1.00  
% 2.32/1.00  fof(f29,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 2.32/1.00    inference(ennf_transformation,[],[f8])).
% 2.32/1.00  
% 2.32/1.00  fof(f30,plain,(
% 2.32/1.00    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 2.32/1.00    inference(flattening,[],[f29])).
% 2.32/1.00  
% 2.32/1.00  fof(f65,plain,(
% 2.32/1.00    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f30])).
% 2.32/1.00  
% 2.32/1.00  fof(f77,plain,(
% 2.32/1.00    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f38])).
% 2.32/1.00  
% 2.32/1.00  fof(f70,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f50])).
% 2.32/1.00  
% 2.32/1.00  fof(f72,plain,(
% 2.32/1.00    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.32/1.00    inference(cnf_transformation,[],[f50])).
% 2.32/1.00  
% 2.32/1.00  cnf(c_18,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.32/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2857,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.32/1.00      | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.32/1.00      | v2_struct_0(X0_47)
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_18]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3550,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2857]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_13,plain,
% 2.32/1.00      ( v1_tex_2(X0,X1)
% 2.32/1.00      | ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2861,plain,
% 2.32/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.32/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.32/1.00      | ~ l1_pre_topc(X1_47)
% 2.32/1.00      | sK1(X1_47,X0_47) = u1_struct_0(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3546,plain,
% 2.32/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X1_47)
% 2.32/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.32/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2861]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4574,plain,
% 2.32/1.00      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.32/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3550,c_3546]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,X1)
% 2.32/1.00      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.32/1.00      | v1_xboole_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2868,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,X1_46)
% 2.32/1.00      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
% 2.32/1.00      | v1_xboole_0(X1_46) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3539,plain,
% 2.32/1.00      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 2.32/1.00      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
% 2.32/1.00      | v1_xboole_0(X1_46) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2868]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_16,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/1.00      | v1_subset_1(X0,X1)
% 2.32/1.00      | X1 = X0 ),
% 2.32/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2859,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.32/1.00      | v1_subset_1(X0_46,X1_46)
% 2.32/1.00      | X1_46 = X0_46 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3548,plain,
% 2.32/1.00      ( X0_46 = X1_46
% 2.32/1.00      | m1_subset_1(X1_46,k1_zfmisc_1(X0_46)) != iProver_top
% 2.32/1.00      | v1_subset_1(X1_46,X0_46) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2859]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3979,plain,
% 2.32/1.00      ( k6_domain_1(X0_46,X1_46) = X0_46
% 2.32/1.00      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 2.32/1.00      | v1_xboole_0(X0_46) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3539,c_3548]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_23,negated_conjecture,
% 2.32/1.00      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2854,negated_conjecture,
% 2.32/1.00      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3553,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2854]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4903,plain,
% 2.32/1.00      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.32/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3979,c_3553]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_27,negated_conjecture,
% 2.32/1.00      ( ~ v2_struct_0(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_28,plain,
% 2.32/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_26,negated_conjecture,
% 2.32/1.00      ( l1_pre_topc(sK2) ),
% 2.32/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_29,plain,
% 2.32/1.00      ( l1_pre_topc(sK2) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_25,negated_conjecture,
% 2.32/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_30,plain,
% 2.32/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3,plain,
% 2.32/1.00      ( v7_struct_0(X0)
% 2.32/1.00      | ~ v1_zfmisc_1(u1_struct_0(X0))
% 2.32/1.00      | ~ l1_struct_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_87,plain,
% 2.32/1.00      ( v7_struct_0(sK2)
% 2.32/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2))
% 2.32/1.00      | ~ l1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1,plain,
% 2.32/1.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_91,plain,
% 2.32/1.00      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2930,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2857]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2929,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2857]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2931,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2929]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_20,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v7_struct_0(k1_tex_2(X1,X0))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2855,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.32/1.00      | v2_struct_0(X0_47)
% 2.32/1.00      | v7_struct_0(k1_tex_2(X0_47,X0_46))
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2936,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | v7_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2855]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4,plain,
% 2.32/1.00      ( ~ v7_struct_0(X0)
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 2.32/1.00      | ~ l1_struct_0(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_362,plain,
% 2.32/1.00      ( ~ v7_struct_0(X0)
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(X0))
% 2.32/1.00      | ~ l1_pre_topc(X0) ),
% 2.32/1.00      inference(resolution,[status(thm)],[c_1,c_4]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2848,plain,
% 2.32/1.00      ( ~ v7_struct_0(X0_47)
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(X0_47))
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_362]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3782,plain,
% 2.32/1.00      ( ~ v7_struct_0(k1_tex_2(X0_47,X0_46))
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46)))
% 2.32/1.00      | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2848]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3784,plain,
% 2.32/1.00      ( ~ v7_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.32/1.00      | ~ l1_pre_topc(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3782]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_6,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2867,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.32/1.00      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.32/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3795,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2867]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3797,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3795]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3796,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) != iProver_top
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47))) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_3795]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3798,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3796]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_9,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,X1)
% 2.32/1.00      | v1_zfmisc_1(X1)
% 2.32/1.00      | v1_xboole_0(X1)
% 2.32/1.00      | k6_domain_1(X1,X0) != X1 ),
% 2.32/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2865,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,X1_46)
% 2.32/1.00      | v1_zfmisc_1(X1_46)
% 2.32/1.00      | v1_xboole_0(X1_46)
% 2.32/1.00      | k6_domain_1(X1_46,X0_46) != X1_46 ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3800,plain,
% 2.32/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2865]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.32/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2869,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.32/1.00      | ~ l1_pre_topc(X1_47)
% 2.32/1.00      | l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3898,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
% 2.32/1.00      | ~ l1_pre_topc(X1_47)
% 2.32/1.00      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2869]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3900,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3898]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_0,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.32/1.00      | ~ v1_subset_1(X0,X1)
% 2.32/1.00      | ~ v1_xboole_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2870,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.32/1.00      | ~ v1_subset_1(X0_46,X1_46)
% 2.32/1.00      | ~ v1_xboole_0(X1_46) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3864,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.32/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2870]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3991,plain,
% 2.32/1.00      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.32/1.00      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3864]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3992,plain,
% 2.32/1.00      ( m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_3991]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4004,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.32/1.00      | u1_struct_0(sK2) = X0_46 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2859]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4107,plain,
% 2.32/1.00      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 2.32/1.00      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,X0_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4004]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4110,plain,
% 2.32/1.00      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.32/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.32/1.00      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4107]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4109,plain,
% 2.32/1.00      ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,X0_46))
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_4107]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4111,plain,
% 2.32/1.00      ( u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.32/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4109]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_24,negated_conjecture,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2853,negated_conjecture,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3554,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2853]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_22,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v7_struct_0(X1)
% 2.32/1.00      | ~ l1_struct_0(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_390,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v7_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X2)
% 2.32/1.00      | X2 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_1]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_391,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v7_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_390]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2846,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.32/1.00      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
% 2.32/1.00      | v2_struct_0(X0_47)
% 2.32/1.00      | ~ v7_struct_0(X0_47)
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_391]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3561,plain,
% 2.32/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4809,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v7_struct_0(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3554,c_3561]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_7,plain,
% 2.32/1.00      ( ~ v1_tex_2(X0,X1)
% 2.32/1.00      | ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v7_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_215,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.32/1.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1495,plain,
% 2.32/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | v2_struct_0(X0)
% 2.32/1.00      | ~ v7_struct_0(X1)
% 2.32/1.00      | ~ l1_pre_topc(X1)
% 2.32/1.00      | k1_tex_2(sK2,sK3) != X0
% 2.32/1.00      | sK2 != X1 ),
% 2.32/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_215]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1496,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | v2_struct_0(sK2)
% 2.32/1.00      | ~ v7_struct_0(sK2)
% 2.32/1.00      | ~ l1_pre_topc(sK2) ),
% 2.32/1.00      inference(unflattening,[status(thm)],[c_1495]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1498,plain,
% 2.32/1.00      ( ~ v7_struct_0(sK2)
% 2.32/1.00      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_1496,c_27,c_26]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1499,plain,
% 2.32/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.32/1.00      | v2_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | ~ v7_struct_0(sK2) ),
% 2.32/1.00      inference(renaming,[status(thm)],[c_1498]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_1500,plain,
% 2.32/1.00      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) = iProver_top
% 2.32/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.32/1.00      | v7_struct_0(sK2) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_1499]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_21,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.32/1.00      | v2_struct_0(X1)
% 2.32/1.00      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2856,plain,
% 2.32/1.00      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.32/1.00      | v2_struct_0(X0_47)
% 2.32/1.00      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.32/1.00      | ~ l1_pre_topc(X0_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2932,plain,
% 2.32/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | v2_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2856]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2934,plain,
% 2.32/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2932]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2946,plain,
% 2.32/1.00      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | v7_struct_0(X0_47) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2948,plain,
% 2.32/1.00      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | v7_struct_0(sK2) != iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2946]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4812,plain,
% 2.32/1.00      ( v7_struct_0(sK2) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4809,c_28,c_29,c_30,c_1500,c_2931,c_2934,c_2948]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4814,plain,
% 2.32/1.00      ( ~ v7_struct_0(sK2) ),
% 2.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4812]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2881,plain,
% 2.32/1.00      ( ~ v1_zfmisc_1(X0_46) | v1_zfmisc_1(X1_46) | X1_46 != X0_46 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4213,plain,
% 2.32/1.00      ( v1_zfmisc_1(X0_46)
% 2.32/1.00      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
% 2.32/1.00      | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2881]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4934,plain,
% 2.32/1.00      ( v1_zfmisc_1(u1_struct_0(X0_47))
% 2.32/1.00      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
% 2.32/1.00      | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4213]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4937,plain,
% 2.32/1.00      ( ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.32/1.00      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.32/1.00      | u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4934]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5125,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2) != iProver_top ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4903,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,
% 2.32/1.00                 c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3900,c_3991,
% 2.32/1.00                 c_3992,c_4110,c_4111,c_4814,c_4937]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5508,plain,
% 2.32/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_4574,c_5125]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3813,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47)
% 2.32/1.00      | ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.32/1.00      | ~ l1_pre_topc(X0_47)
% 2.32/1.00      | sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(k1_tex_2(X0_47,X0_46)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2861]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3815,plain,
% 2.32/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ l1_pre_topc(sK2)
% 2.32/1.00      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_3813]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4925,plain,
% 2.32/1.00      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.32/1.00      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.32/1.00      | v1_xboole_0(u1_struct_0(sK2))
% 2.32/1.00      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 2.32/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4903]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5916,plain,
% 2.32/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_5508,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,
% 2.32/1.00                 c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3816,c_3900,
% 2.32/1.00                 c_3991,c_3992,c_4110,c_4111,c_4814,c_4903,c_4937]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_14,plain,
% 2.32/1.00      ( v1_tex_2(X0,X1)
% 2.32/1.00      | ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2860,plain,
% 2.32/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.32/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.32/1.00      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.32/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3547,plain,
% 2.32/1.00      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.32/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.32/1.00      | m1_subset_1(sK1(X1_47,X0_47),k1_zfmisc_1(u1_struct_0(X1_47))) = iProver_top
% 2.32/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2860]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4884,plain,
% 2.32/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.32/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.32/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.32/1.00      | v1_subset_1(sK1(X0_47,X1_47),u1_struct_0(X0_47)) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3547,c_3548]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_12,plain,
% 2.32/1.00      ( v1_tex_2(X0,X1)
% 2.32/1.00      | ~ m1_pre_topc(X0,X1)
% 2.32/1.00      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.32/1.00      | ~ l1_pre_topc(X1) ),
% 2.32/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2862,plain,
% 2.32/1.00      ( v1_tex_2(X0_47,X1_47)
% 2.32/1.00      | ~ m1_pre_topc(X0_47,X1_47)
% 2.32/1.00      | ~ v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47))
% 2.32/1.00      | ~ l1_pre_topc(X1_47) ),
% 2.32/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_3545,plain,
% 2.32/1.00      ( v1_tex_2(X0_47,X1_47) = iProver_top
% 2.32/1.00      | m1_pre_topc(X0_47,X1_47) != iProver_top
% 2.32/1.00      | v1_subset_1(sK1(X1_47,X0_47),u1_struct_0(X1_47)) != iProver_top
% 2.32/1.00      | l1_pre_topc(X1_47) != iProver_top ),
% 2.32/1.00      inference(predicate_to_equality,[status(thm)],[c_2862]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5786,plain,
% 2.32/1.00      ( sK1(X0_47,X1_47) = u1_struct_0(X0_47)
% 2.32/1.00      | v1_tex_2(X1_47,X0_47) = iProver_top
% 2.32/1.00      | m1_pre_topc(X1_47,X0_47) != iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(forward_subsumption_resolution,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_4884,c_3545]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5788,plain,
% 2.32/1.00      ( sK1(X0_47,k1_tex_2(X0_47,X0_46)) = u1_struct_0(X0_47)
% 2.32/1.00      | v1_tex_2(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.32/1.00      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.32/1.00      | v2_struct_0(X0_47) = iProver_top
% 2.32/1.00      | l1_pre_topc(X0_47) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_3550,c_5786]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5798,plain,
% 2.32/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(superposition,[status(thm)],[c_5788,c_5125]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5790,plain,
% 2.32/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2)
% 2.32/1.00      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.32/1.00      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.32/1.00      | v2_struct_0(sK2) = iProver_top
% 2.32/1.00      | l1_pre_topc(sK2) != iProver_top ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_5788]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5892,plain,
% 2.32/1.00      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.32/1.00      inference(global_propositional_subsumption,
% 2.32/1.00                [status(thm)],
% 2.32/1.00                [c_5798,c_27,c_28,c_26,c_29,c_25,c_30,c_87,c_91,c_2930,
% 2.32/1.00                 c_2931,c_2936,c_3784,c_3797,c_3798,c_3800,c_3900,c_3991,
% 2.32/1.00                 c_3992,c_4110,c_4111,c_4814,c_4903,c_4937,c_5790]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_5918,plain,
% 2.32/1.00      ( u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.32/1.00      inference(light_normalisation,[status(thm)],[c_5916,c_5892]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2874,plain,
% 2.32/1.00      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4010,plain,
% 2.32/1.00      ( X0_46 != X1_46
% 2.32/1.00      | u1_struct_0(sK2) != X1_46
% 2.32/1.00      | u1_struct_0(sK2) = X0_46 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2874]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4124,plain,
% 2.32/1.00      ( X0_46 != u1_struct_0(sK2)
% 2.32/1.00      | u1_struct_0(sK2) = X0_46
% 2.32/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4010]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4429,plain,
% 2.32/1.00      ( u1_struct_0(X0_47) != u1_struct_0(sK2)
% 2.32/1.00      | u1_struct_0(sK2) = u1_struct_0(X0_47)
% 2.32/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4124]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_4708,plain,
% 2.32/1.00      ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
% 2.32/1.00      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.32/1.00      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_4429]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2873,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2901,plain,
% 2.32/1.00      ( sK2 = sK2 ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2873]) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2880,plain,
% 2.32/1.00      ( X0_47 != X1_47 | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
% 2.32/1.00      theory(equality) ).
% 2.32/1.00  
% 2.32/1.00  cnf(c_2892,plain,
% 2.32/1.00      ( sK2 != sK2 | u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.32/1.00      inference(instantiation,[status(thm)],[c_2880]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(contradiction,plain,
% 2.32/1.01      ( $false ),
% 2.32/1.01      inference(minisat,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_5918,c_4937,c_4814,c_4708,c_3900,c_3784,c_2936,c_2930,
% 2.32/1.01                 c_2901,c_2892,c_91,c_87,c_25,c_26,c_27]) ).
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  ------                               Statistics
% 2.32/1.01  
% 2.32/1.01  ------ General
% 2.32/1.01  
% 2.32/1.01  abstr_ref_over_cycles:                  0
% 2.32/1.01  abstr_ref_under_cycles:                 0
% 2.32/1.01  gc_basic_clause_elim:                   0
% 2.32/1.01  forced_gc_time:                         0
% 2.32/1.01  parsing_time:                           0.009
% 2.32/1.01  unif_index_cands_time:                  0.
% 2.32/1.01  unif_index_add_time:                    0.
% 2.32/1.01  orderings_time:                         0.
% 2.32/1.01  out_proof_time:                         0.013
% 2.32/1.01  total_time:                             0.176
% 2.32/1.01  num_of_symbols:                         51
% 2.32/1.01  num_of_terms:                           3516
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing
% 2.32/1.01  
% 2.32/1.01  num_of_splits:                          0
% 2.32/1.01  num_of_split_atoms:                     0
% 2.32/1.01  num_of_reused_defs:                     0
% 2.32/1.01  num_eq_ax_congr_red:                    16
% 2.32/1.01  num_of_sem_filtered_clauses:            1
% 2.32/1.01  num_of_subtypes:                        2
% 2.32/1.01  monotx_restored_types:                  1
% 2.32/1.01  sat_num_of_epr_types:                   0
% 2.32/1.01  sat_num_of_non_cyclic_types:            0
% 2.32/1.01  sat_guarded_non_collapsed_types:        0
% 2.32/1.01  num_pure_diseq_elim:                    0
% 2.32/1.01  simp_replaced_by:                       0
% 2.32/1.01  res_preprocessed:                       132
% 2.32/1.01  prep_upred:                             0
% 2.32/1.01  prep_unflattend:                        101
% 2.32/1.01  smt_new_axioms:                         0
% 2.32/1.01  pred_elim_cands:                        9
% 2.32/1.01  pred_elim:                              1
% 2.32/1.01  pred_elim_cl:                           1
% 2.32/1.01  pred_elim_cycles:                       13
% 2.32/1.01  merged_defs:                            8
% 2.32/1.01  merged_defs_ncl:                        0
% 2.32/1.01  bin_hyper_res:                          8
% 2.32/1.01  prep_cycles:                            4
% 2.32/1.01  pred_elim_time:                         0.04
% 2.32/1.01  splitting_time:                         0.
% 2.32/1.01  sem_filter_time:                        0.
% 2.32/1.01  monotx_time:                            0.001
% 2.32/1.01  subtype_inf_time:                       0.001
% 2.32/1.01  
% 2.32/1.01  ------ Problem properties
% 2.32/1.01  
% 2.32/1.01  clauses:                                25
% 2.32/1.01  conjectures:                            5
% 2.32/1.01  epr:                                    4
% 2.32/1.01  horn:                                   14
% 2.32/1.01  ground:                                 5
% 2.32/1.01  unary:                                  3
% 2.32/1.01  binary:                                 3
% 2.32/1.01  lits:                                   79
% 2.32/1.01  lits_eq:                                4
% 2.32/1.01  fd_pure:                                0
% 2.32/1.01  fd_pseudo:                              0
% 2.32/1.01  fd_cond:                                0
% 2.32/1.01  fd_pseudo_cond:                         1
% 2.32/1.01  ac_symbols:                             0
% 2.32/1.01  
% 2.32/1.01  ------ Propositional Solver
% 2.32/1.01  
% 2.32/1.01  prop_solver_calls:                      28
% 2.32/1.01  prop_fast_solver_calls:                 1551
% 2.32/1.01  smt_solver_calls:                       0
% 2.32/1.01  smt_fast_solver_calls:                  0
% 2.32/1.01  prop_num_of_clauses:                    1186
% 2.32/1.01  prop_preprocess_simplified:             5492
% 2.32/1.01  prop_fo_subsumed:                       45
% 2.32/1.01  prop_solver_time:                       0.
% 2.32/1.01  smt_solver_time:                        0.
% 2.32/1.01  smt_fast_solver_time:                   0.
% 2.32/1.01  prop_fast_solver_time:                  0.
% 2.32/1.01  prop_unsat_core_time:                   0.
% 2.32/1.01  
% 2.32/1.01  ------ QBF
% 2.32/1.01  
% 2.32/1.01  qbf_q_res:                              0
% 2.32/1.01  qbf_num_tautologies:                    0
% 2.32/1.01  qbf_prep_cycles:                        0
% 2.32/1.01  
% 2.32/1.01  ------ BMC1
% 2.32/1.01  
% 2.32/1.01  bmc1_current_bound:                     -1
% 2.32/1.01  bmc1_last_solved_bound:                 -1
% 2.32/1.01  bmc1_unsat_core_size:                   -1
% 2.32/1.01  bmc1_unsat_core_parents_size:           -1
% 2.32/1.01  bmc1_merge_next_fun:                    0
% 2.32/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation
% 2.32/1.01  
% 2.32/1.01  inst_num_of_clauses:                    328
% 2.32/1.01  inst_num_in_passive:                    26
% 2.32/1.01  inst_num_in_active:                     211
% 2.32/1.01  inst_num_in_unprocessed:                91
% 2.32/1.01  inst_num_of_loops:                      260
% 2.32/1.01  inst_num_of_learning_restarts:          0
% 2.32/1.01  inst_num_moves_active_passive:          45
% 2.32/1.01  inst_lit_activity:                      0
% 2.32/1.01  inst_lit_activity_moves:                0
% 2.32/1.01  inst_num_tautologies:                   0
% 2.32/1.01  inst_num_prop_implied:                  0
% 2.32/1.01  inst_num_existing_simplified:           0
% 2.32/1.01  inst_num_eq_res_simplified:             0
% 2.32/1.01  inst_num_child_elim:                    0
% 2.32/1.01  inst_num_of_dismatching_blockings:      164
% 2.32/1.01  inst_num_of_non_proper_insts:           393
% 2.32/1.01  inst_num_of_duplicates:                 0
% 2.32/1.01  inst_inst_num_from_inst_to_res:         0
% 2.32/1.01  inst_dismatching_checking_time:         0.
% 2.32/1.01  
% 2.32/1.01  ------ Resolution
% 2.32/1.01  
% 2.32/1.01  res_num_of_clauses:                     0
% 2.32/1.01  res_num_in_passive:                     0
% 2.32/1.01  res_num_in_active:                      0
% 2.32/1.01  res_num_of_loops:                       136
% 2.32/1.01  res_forward_subset_subsumed:            37
% 2.32/1.01  res_backward_subset_subsumed:           0
% 2.32/1.01  res_forward_subsumed:                   0
% 2.32/1.01  res_backward_subsumed:                  0
% 2.32/1.01  res_forward_subsumption_resolution:     2
% 2.32/1.01  res_backward_subsumption_resolution:    0
% 2.32/1.01  res_clause_to_clause_subsumption:       151
% 2.32/1.01  res_orphan_elimination:                 0
% 2.32/1.01  res_tautology_del:                      82
% 2.32/1.01  res_num_eq_res_simplified:              0
% 2.32/1.01  res_num_sel_changes:                    0
% 2.32/1.01  res_moves_from_active_to_pass:          0
% 2.32/1.01  
% 2.32/1.01  ------ Superposition
% 2.32/1.01  
% 2.32/1.01  sup_time_total:                         0.
% 2.32/1.01  sup_time_generating:                    0.
% 2.32/1.01  sup_time_sim_full:                      0.
% 2.32/1.01  sup_time_sim_immed:                     0.
% 2.32/1.01  
% 2.32/1.01  sup_num_of_clauses:                     58
% 2.32/1.01  sup_num_in_active:                      50
% 2.32/1.01  sup_num_in_passive:                     8
% 2.32/1.01  sup_num_of_loops:                       51
% 2.32/1.01  sup_fw_superposition:                   15
% 2.32/1.01  sup_bw_superposition:                   26
% 2.32/1.01  sup_immediate_simplified:               2
% 2.32/1.01  sup_given_eliminated:                   0
% 2.32/1.01  comparisons_done:                       0
% 2.32/1.01  comparisons_avoided:                    0
% 2.32/1.01  
% 2.32/1.01  ------ Simplifications
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  sim_fw_subset_subsumed:                 2
% 2.32/1.01  sim_bw_subset_subsumed:                 2
% 2.32/1.01  sim_fw_subsumed:                        0
% 2.32/1.01  sim_bw_subsumed:                        0
% 2.32/1.01  sim_fw_subsumption_res:                 1
% 2.32/1.01  sim_bw_subsumption_res:                 0
% 2.32/1.01  sim_tautology_del:                      4
% 2.32/1.01  sim_eq_tautology_del:                   1
% 2.32/1.01  sim_eq_res_simp:                        0
% 2.32/1.01  sim_fw_demodulated:                     0
% 2.32/1.01  sim_bw_demodulated:                     0
% 2.32/1.01  sim_light_normalised:                   1
% 2.32/1.01  sim_joinable_taut:                      0
% 2.32/1.01  sim_joinable_simp:                      0
% 2.32/1.01  sim_ac_normalised:                      0
% 2.32/1.01  sim_smt_subsumption:                    0
% 2.32/1.01  
%------------------------------------------------------------------------------
