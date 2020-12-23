%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:38 EST 2020

% Result     : Theorem 1.44s
% Output     : CNFRefutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 966 expanded)
%              Number of clauses        :   80 ( 246 expanded)
%              Number of leaves         :   10 ( 210 expanded)
%              Depth                    :   24
%              Number of atoms          :  496 (5340 expanded)
%              Number of equality atoms :   83 ( 134 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
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

fof(f32,plain,
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

fof(f34,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tex_2(X1,X0)
            & ~ v2_struct_0(X1) )
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_tex_2(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2)
                & ~ v2_struct_0(X2) )
             => ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_tex_2(X0,X1) = X2
              <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_tex_2(X0,X1) = X2
                  | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1) )
                & ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
                  | k1_tex_2(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f52,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_722,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_pre_topc(k1_tex_2(X1,X0),X1)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_722])).

cnf(c_18,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_727,plain,
    ( m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_723,c_18])).

cnf(c_728,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,X0),sK1) ),
    inference(renaming,[status(thm)],[c_727])).

cnf(c_2358,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) ),
    inference(subtyping,[status(esa)],[c_728])).

cnf(c_2670,plain,
    ( m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_786,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_tex_2(X0,X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_787,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | v1_tex_2(X0,sK1)
    | sK0(sK1,X0) = u1_struct_0(X0) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_2356,plain,
    ( ~ m1_pre_topc(X0_45,sK1)
    | v1_tex_2(X0_45,sK1)
    | sK0(sK1,X0_45) = u1_struct_0(X0_45) ),
    inference(subtyping,[status(esa)],[c_787])).

cnf(c_2672,plain,
    ( sK0(sK1,X0_45) = u1_struct_0(X0_45)
    | m1_pre_topc(X0_45,sK1) != iProver_top
    | v1_tex_2(X0_45,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2356])).

cnf(c_3009,plain,
    ( sK0(sK1,k1_tex_2(sK1,X0_44)) = u1_struct_0(k1_tex_2(sK1,X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2670,c_2672])).

cnf(c_14,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2366,negated_conjecture,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2662,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_13])).

cnf(c_259,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_647,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | v7_struct_0(X1)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_259,c_17])).

cnf(c_648,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
    | v7_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_652,plain,
    ( v7_struct_0(sK1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_18])).

cnf(c_653,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
    | v7_struct_0(sK1) ),
    inference(renaming,[status(thm)],[c_652])).

cnf(c_2360,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_44),u1_struct_0(sK1))
    | v7_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_653])).

cnf(c_2404,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v7_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2360])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_801,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ v7_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_802,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tex_2(X0,sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_806,plain,
    ( v2_struct_0(X0)
    | ~ v7_struct_0(sK1)
    | ~ v1_tex_2(X0,sK1)
    | ~ m1_pre_topc(X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_18])).

cnf(c_807,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ v1_tex_2(X0,sK1)
    | ~ v7_struct_0(sK1)
    | v2_struct_0(X0) ),
    inference(renaming,[status(thm)],[c_806])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_687,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,X0))
    | v2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_691,plain,
    ( ~ v2_struct_0(k1_tex_2(sK1,X0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_687,c_18])).

cnf(c_692,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v2_struct_0(k1_tex_2(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_691])).

cnf(c_915,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_pre_topc(X1,sK1)
    | ~ v1_tex_2(X1,sK1)
    | ~ v7_struct_0(sK1)
    | k1_tex_2(sK1,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_807,c_692])).

cnf(c_916,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
    | ~ v1_tex_2(k1_tex_2(sK1,X0),sK1)
    | ~ v7_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_915])).

cnf(c_920,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,X0),sK1)
    | ~ v7_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_916,c_18,c_723])).

cnf(c_2353,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,X0_44),sK1)
    | ~ v7_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_920])).

cnf(c_2421,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | ~ v7_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2353])).

cnf(c_2448,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2366,c_16,c_14,c_2404,c_2421])).

cnf(c_2450,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_2802,plain,
    ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2662,c_2450])).

cnf(c_3136,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3009,c_2802])).

cnf(c_2410,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2358])).

cnf(c_2791,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,X0_44),sK1)
    | v1_tex_2(k1_tex_2(sK1,X0_44),sK1)
    | sK0(sK1,k1_tex_2(sK1,X0_44)) = u1_struct_0(k1_tex_2(sK1,X0_44)) ),
    inference(instantiation,[status(thm)],[c_2356])).

cnf(c_2793,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1)
    | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_3139,plain,
    ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3136,c_16,c_14,c_2404,c_2410,c_2421,c_2793])).

cnf(c_3,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v1_tex_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_611,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | v1_tex_2(X1,X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_612,plain,
    ( ~ v1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0,sK1)
    | v1_tex_2(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_2362,plain,
    ( ~ v1_subset_1(sK0(sK1,X0_45),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_45,sK1)
    | v1_tex_2(X0_45,sK1) ),
    inference(subtyping,[status(esa)],[c_612])).

cnf(c_2666,plain,
    ( v1_subset_1(sK0(sK1,X0_45),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_45,sK1) != iProver_top
    | v1_tex_2(X0_45,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2362])).

cnf(c_3142,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3139,c_2666])).

cnf(c_2364,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2664,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2364])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_pre_topc(k1_tex_2(X1,X0),X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_113,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_11,c_10,c_9])).

cnf(c_114,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_113])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_114,c_17])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_18])).

cnf(c_2359,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),X0_44) = u1_struct_0(k1_tex_2(sK1,X0_44)) ),
    inference(subtyping,[status(esa)],[c_673])).

cnf(c_2669,plain,
    ( k6_domain_1(u1_struct_0(sK1),X0_44) = u1_struct_0(k1_tex_2(sK1,X0_44))
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2359])).

cnf(c_2859,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_2664,c_2669])).

cnf(c_15,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2365,negated_conjecture,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2663,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2365])).

cnf(c_22,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
    | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2821,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2663,c_22,c_2450])).

cnf(c_2861,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2859,c_2821])).

cnf(c_2409,plain,
    ( m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2358])).

cnf(c_2411,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2409])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3142,c_2861,c_2450,c_2411,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:03:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.44/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.44/1.02  
% 1.44/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.44/1.02  
% 1.44/1.02  ------  iProver source info
% 1.44/1.02  
% 1.44/1.02  git: date: 2020-06-30 10:37:57 +0100
% 1.44/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.44/1.02  git: non_committed_changes: false
% 1.44/1.02  git: last_make_outside_of_git: false
% 1.44/1.02  
% 1.44/1.02  ------ 
% 1.44/1.02  
% 1.44/1.02  ------ Input Options
% 1.44/1.02  
% 1.44/1.02  --out_options                           all
% 1.44/1.02  --tptp_safe_out                         true
% 1.44/1.02  --problem_path                          ""
% 1.44/1.02  --include_path                          ""
% 1.44/1.02  --clausifier                            res/vclausify_rel
% 1.44/1.02  --clausifier_options                    --mode clausify
% 1.44/1.02  --stdin                                 false
% 1.44/1.02  --stats_out                             all
% 1.44/1.02  
% 1.44/1.02  ------ General Options
% 1.44/1.02  
% 1.44/1.02  --fof                                   false
% 1.44/1.02  --time_out_real                         305.
% 1.44/1.02  --time_out_virtual                      -1.
% 1.44/1.02  --symbol_type_check                     false
% 1.44/1.02  --clausify_out                          false
% 1.44/1.02  --sig_cnt_out                           false
% 1.44/1.02  --trig_cnt_out                          false
% 1.44/1.02  --trig_cnt_out_tolerance                1.
% 1.44/1.02  --trig_cnt_out_sk_spl                   false
% 1.44/1.02  --abstr_cl_out                          false
% 1.44/1.02  
% 1.44/1.02  ------ Global Options
% 1.44/1.02  
% 1.44/1.02  --schedule                              default
% 1.44/1.02  --add_important_lit                     false
% 1.44/1.02  --prop_solver_per_cl                    1000
% 1.44/1.02  --min_unsat_core                        false
% 1.44/1.02  --soft_assumptions                      false
% 1.44/1.02  --soft_lemma_size                       3
% 1.44/1.02  --prop_impl_unit_size                   0
% 1.44/1.02  --prop_impl_unit                        []
% 1.44/1.02  --share_sel_clauses                     true
% 1.44/1.02  --reset_solvers                         false
% 1.44/1.02  --bc_imp_inh                            [conj_cone]
% 1.44/1.02  --conj_cone_tolerance                   3.
% 1.44/1.02  --extra_neg_conj                        none
% 1.44/1.02  --large_theory_mode                     true
% 1.44/1.02  --prolific_symb_bound                   200
% 1.44/1.02  --lt_threshold                          2000
% 1.44/1.02  --clause_weak_htbl                      true
% 1.44/1.02  --gc_record_bc_elim                     false
% 1.44/1.02  
% 1.44/1.02  ------ Preprocessing Options
% 1.44/1.02  
% 1.44/1.02  --preprocessing_flag                    true
% 1.44/1.02  --time_out_prep_mult                    0.1
% 1.44/1.02  --splitting_mode                        input
% 1.44/1.02  --splitting_grd                         true
% 1.44/1.02  --splitting_cvd                         false
% 1.44/1.02  --splitting_cvd_svl                     false
% 1.44/1.02  --splitting_nvd                         32
% 1.44/1.02  --sub_typing                            true
% 1.44/1.02  --prep_gs_sim                           true
% 1.44/1.02  --prep_unflatten                        true
% 1.44/1.02  --prep_res_sim                          true
% 1.44/1.02  --prep_upred                            true
% 1.44/1.02  --prep_sem_filter                       exhaustive
% 1.44/1.02  --prep_sem_filter_out                   false
% 1.44/1.02  --pred_elim                             true
% 1.44/1.02  --res_sim_input                         true
% 1.44/1.02  --eq_ax_congr_red                       true
% 1.44/1.02  --pure_diseq_elim                       true
% 1.44/1.02  --brand_transform                       false
% 1.44/1.02  --non_eq_to_eq                          false
% 1.44/1.02  --prep_def_merge                        true
% 1.44/1.02  --prep_def_merge_prop_impl              false
% 1.44/1.02  --prep_def_merge_mbd                    true
% 1.44/1.02  --prep_def_merge_tr_red                 false
% 1.44/1.02  --prep_def_merge_tr_cl                  false
% 1.44/1.02  --smt_preprocessing                     true
% 1.44/1.02  --smt_ac_axioms                         fast
% 1.44/1.02  --preprocessed_out                      false
% 1.44/1.02  --preprocessed_stats                    false
% 1.44/1.02  
% 1.44/1.02  ------ Abstraction refinement Options
% 1.44/1.02  
% 1.44/1.02  --abstr_ref                             []
% 1.44/1.02  --abstr_ref_prep                        false
% 1.44/1.02  --abstr_ref_until_sat                   false
% 1.44/1.02  --abstr_ref_sig_restrict                funpre
% 1.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/1.02  --abstr_ref_under                       []
% 1.44/1.02  
% 1.44/1.02  ------ SAT Options
% 1.44/1.02  
% 1.44/1.02  --sat_mode                              false
% 1.44/1.02  --sat_fm_restart_options                ""
% 1.44/1.02  --sat_gr_def                            false
% 1.44/1.02  --sat_epr_types                         true
% 1.44/1.02  --sat_non_cyclic_types                  false
% 1.44/1.02  --sat_finite_models                     false
% 1.44/1.02  --sat_fm_lemmas                         false
% 1.44/1.02  --sat_fm_prep                           false
% 1.44/1.02  --sat_fm_uc_incr                        true
% 1.44/1.02  --sat_out_model                         small
% 1.44/1.02  --sat_out_clauses                       false
% 1.44/1.02  
% 1.44/1.02  ------ QBF Options
% 1.44/1.02  
% 1.44/1.02  --qbf_mode                              false
% 1.44/1.02  --qbf_elim_univ                         false
% 1.44/1.02  --qbf_dom_inst                          none
% 1.44/1.02  --qbf_dom_pre_inst                      false
% 1.44/1.02  --qbf_sk_in                             false
% 1.44/1.02  --qbf_pred_elim                         true
% 1.44/1.02  --qbf_split                             512
% 1.44/1.02  
% 1.44/1.02  ------ BMC1 Options
% 1.44/1.02  
% 1.44/1.02  --bmc1_incremental                      false
% 1.44/1.02  --bmc1_axioms                           reachable_all
% 1.44/1.02  --bmc1_min_bound                        0
% 1.44/1.02  --bmc1_max_bound                        -1
% 1.44/1.02  --bmc1_max_bound_default                -1
% 1.44/1.02  --bmc1_symbol_reachability              true
% 1.44/1.02  --bmc1_property_lemmas                  false
% 1.44/1.02  --bmc1_k_induction                      false
% 1.44/1.02  --bmc1_non_equiv_states                 false
% 1.44/1.02  --bmc1_deadlock                         false
% 1.44/1.02  --bmc1_ucm                              false
% 1.44/1.02  --bmc1_add_unsat_core                   none
% 1.44/1.02  --bmc1_unsat_core_children              false
% 1.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/1.02  --bmc1_out_stat                         full
% 1.44/1.02  --bmc1_ground_init                      false
% 1.44/1.02  --bmc1_pre_inst_next_state              false
% 1.44/1.02  --bmc1_pre_inst_state                   false
% 1.44/1.02  --bmc1_pre_inst_reach_state             false
% 1.44/1.02  --bmc1_out_unsat_core                   false
% 1.44/1.02  --bmc1_aig_witness_out                  false
% 1.44/1.02  --bmc1_verbose                          false
% 1.44/1.02  --bmc1_dump_clauses_tptp                false
% 1.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.44/1.02  --bmc1_dump_file                        -
% 1.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.44/1.02  --bmc1_ucm_extend_mode                  1
% 1.44/1.02  --bmc1_ucm_init_mode                    2
% 1.44/1.02  --bmc1_ucm_cone_mode                    none
% 1.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.44/1.02  --bmc1_ucm_relax_model                  4
% 1.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/1.02  --bmc1_ucm_layered_model                none
% 1.44/1.02  --bmc1_ucm_max_lemma_size               10
% 1.44/1.02  
% 1.44/1.02  ------ AIG Options
% 1.44/1.02  
% 1.44/1.02  --aig_mode                              false
% 1.44/1.02  
% 1.44/1.02  ------ Instantiation Options
% 1.44/1.02  
% 1.44/1.02  --instantiation_flag                    true
% 1.44/1.02  --inst_sos_flag                         false
% 1.44/1.02  --inst_sos_phase                        true
% 1.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/1.02  --inst_lit_sel_side                     num_symb
% 1.44/1.02  --inst_solver_per_active                1400
% 1.44/1.02  --inst_solver_calls_frac                1.
% 1.44/1.02  --inst_passive_queue_type               priority_queues
% 1.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/1.02  --inst_passive_queues_freq              [25;2]
% 1.44/1.02  --inst_dismatching                      true
% 1.44/1.02  --inst_eager_unprocessed_to_passive     true
% 1.44/1.02  --inst_prop_sim_given                   true
% 1.44/1.02  --inst_prop_sim_new                     false
% 1.44/1.02  --inst_subs_new                         false
% 1.44/1.02  --inst_eq_res_simp                      false
% 1.44/1.02  --inst_subs_given                       false
% 1.44/1.02  --inst_orphan_elimination               true
% 1.44/1.02  --inst_learning_loop_flag               true
% 1.44/1.02  --inst_learning_start                   3000
% 1.44/1.02  --inst_learning_factor                  2
% 1.44/1.02  --inst_start_prop_sim_after_learn       3
% 1.44/1.02  --inst_sel_renew                        solver
% 1.44/1.02  --inst_lit_activity_flag                true
% 1.44/1.02  --inst_restr_to_given                   false
% 1.44/1.02  --inst_activity_threshold               500
% 1.44/1.02  --inst_out_proof                        true
% 1.44/1.02  
% 1.44/1.02  ------ Resolution Options
% 1.44/1.02  
% 1.44/1.02  --resolution_flag                       true
% 1.44/1.02  --res_lit_sel                           adaptive
% 1.44/1.02  --res_lit_sel_side                      none
% 1.44/1.02  --res_ordering                          kbo
% 1.44/1.02  --res_to_prop_solver                    active
% 1.44/1.02  --res_prop_simpl_new                    false
% 1.44/1.02  --res_prop_simpl_given                  true
% 1.44/1.02  --res_passive_queue_type                priority_queues
% 1.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/1.02  --res_passive_queues_freq               [15;5]
% 1.44/1.02  --res_forward_subs                      full
% 1.44/1.02  --res_backward_subs                     full
% 1.44/1.02  --res_forward_subs_resolution           true
% 1.44/1.02  --res_backward_subs_resolution          true
% 1.44/1.02  --res_orphan_elimination                true
% 1.44/1.02  --res_time_limit                        2.
% 1.44/1.02  --res_out_proof                         true
% 1.44/1.02  
% 1.44/1.02  ------ Superposition Options
% 1.44/1.02  
% 1.44/1.02  --superposition_flag                    true
% 1.44/1.02  --sup_passive_queue_type                priority_queues
% 1.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.44/1.02  --demod_completeness_check              fast
% 1.44/1.02  --demod_use_ground                      true
% 1.44/1.02  --sup_to_prop_solver                    passive
% 1.44/1.02  --sup_prop_simpl_new                    true
% 1.44/1.02  --sup_prop_simpl_given                  true
% 1.44/1.02  --sup_fun_splitting                     false
% 1.44/1.02  --sup_smt_interval                      50000
% 1.44/1.02  
% 1.44/1.02  ------ Superposition Simplification Setup
% 1.44/1.02  
% 1.44/1.02  --sup_indices_passive                   []
% 1.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_full_bw                           [BwDemod]
% 1.44/1.02  --sup_immed_triv                        [TrivRules]
% 1.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_immed_bw_main                     []
% 1.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.02  
% 1.44/1.02  ------ Combination Options
% 1.44/1.02  
% 1.44/1.02  --comb_res_mult                         3
% 1.44/1.02  --comb_sup_mult                         2
% 1.44/1.02  --comb_inst_mult                        10
% 1.44/1.02  
% 1.44/1.02  ------ Debug Options
% 1.44/1.02  
% 1.44/1.02  --dbg_backtrace                         false
% 1.44/1.02  --dbg_dump_prop_clauses                 false
% 1.44/1.02  --dbg_dump_prop_clauses_file            -
% 1.44/1.02  --dbg_out_stat                          false
% 1.44/1.02  ------ Parsing...
% 1.44/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.44/1.02  
% 1.44/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.44/1.02  
% 1.44/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.44/1.02  
% 1.44/1.02  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.44/1.02  ------ Proving...
% 1.44/1.02  ------ Problem Properties 
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  clauses                                 14
% 1.44/1.02  conjectures                             3
% 1.44/1.02  EPR                                     1
% 1.44/1.02  Horn                                    10
% 1.44/1.02  unary                                   1
% 1.44/1.02  binary                                  4
% 1.44/1.02  lits                                    38
% 1.44/1.02  lits eq                                 4
% 1.44/1.02  fd_pure                                 0
% 1.44/1.02  fd_pseudo                               0
% 1.44/1.02  fd_cond                                 0
% 1.44/1.02  fd_pseudo_cond                          0
% 1.44/1.02  AC symbols                              0
% 1.44/1.02  
% 1.44/1.02  ------ Schedule dynamic 5 is on 
% 1.44/1.02  
% 1.44/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  ------ 
% 1.44/1.02  Current options:
% 1.44/1.02  ------ 
% 1.44/1.02  
% 1.44/1.02  ------ Input Options
% 1.44/1.02  
% 1.44/1.02  --out_options                           all
% 1.44/1.02  --tptp_safe_out                         true
% 1.44/1.02  --problem_path                          ""
% 1.44/1.02  --include_path                          ""
% 1.44/1.02  --clausifier                            res/vclausify_rel
% 1.44/1.02  --clausifier_options                    --mode clausify
% 1.44/1.02  --stdin                                 false
% 1.44/1.02  --stats_out                             all
% 1.44/1.02  
% 1.44/1.02  ------ General Options
% 1.44/1.02  
% 1.44/1.02  --fof                                   false
% 1.44/1.02  --time_out_real                         305.
% 1.44/1.02  --time_out_virtual                      -1.
% 1.44/1.02  --symbol_type_check                     false
% 1.44/1.02  --clausify_out                          false
% 1.44/1.02  --sig_cnt_out                           false
% 1.44/1.02  --trig_cnt_out                          false
% 1.44/1.02  --trig_cnt_out_tolerance                1.
% 1.44/1.02  --trig_cnt_out_sk_spl                   false
% 1.44/1.02  --abstr_cl_out                          false
% 1.44/1.02  
% 1.44/1.02  ------ Global Options
% 1.44/1.02  
% 1.44/1.02  --schedule                              default
% 1.44/1.02  --add_important_lit                     false
% 1.44/1.02  --prop_solver_per_cl                    1000
% 1.44/1.02  --min_unsat_core                        false
% 1.44/1.02  --soft_assumptions                      false
% 1.44/1.02  --soft_lemma_size                       3
% 1.44/1.02  --prop_impl_unit_size                   0
% 1.44/1.02  --prop_impl_unit                        []
% 1.44/1.02  --share_sel_clauses                     true
% 1.44/1.02  --reset_solvers                         false
% 1.44/1.02  --bc_imp_inh                            [conj_cone]
% 1.44/1.02  --conj_cone_tolerance                   3.
% 1.44/1.02  --extra_neg_conj                        none
% 1.44/1.02  --large_theory_mode                     true
% 1.44/1.02  --prolific_symb_bound                   200
% 1.44/1.02  --lt_threshold                          2000
% 1.44/1.02  --clause_weak_htbl                      true
% 1.44/1.02  --gc_record_bc_elim                     false
% 1.44/1.02  
% 1.44/1.02  ------ Preprocessing Options
% 1.44/1.02  
% 1.44/1.02  --preprocessing_flag                    true
% 1.44/1.02  --time_out_prep_mult                    0.1
% 1.44/1.02  --splitting_mode                        input
% 1.44/1.02  --splitting_grd                         true
% 1.44/1.02  --splitting_cvd                         false
% 1.44/1.02  --splitting_cvd_svl                     false
% 1.44/1.02  --splitting_nvd                         32
% 1.44/1.02  --sub_typing                            true
% 1.44/1.02  --prep_gs_sim                           true
% 1.44/1.02  --prep_unflatten                        true
% 1.44/1.02  --prep_res_sim                          true
% 1.44/1.02  --prep_upred                            true
% 1.44/1.02  --prep_sem_filter                       exhaustive
% 1.44/1.02  --prep_sem_filter_out                   false
% 1.44/1.02  --pred_elim                             true
% 1.44/1.02  --res_sim_input                         true
% 1.44/1.02  --eq_ax_congr_red                       true
% 1.44/1.02  --pure_diseq_elim                       true
% 1.44/1.02  --brand_transform                       false
% 1.44/1.02  --non_eq_to_eq                          false
% 1.44/1.02  --prep_def_merge                        true
% 1.44/1.02  --prep_def_merge_prop_impl              false
% 1.44/1.02  --prep_def_merge_mbd                    true
% 1.44/1.02  --prep_def_merge_tr_red                 false
% 1.44/1.02  --prep_def_merge_tr_cl                  false
% 1.44/1.02  --smt_preprocessing                     true
% 1.44/1.02  --smt_ac_axioms                         fast
% 1.44/1.02  --preprocessed_out                      false
% 1.44/1.02  --preprocessed_stats                    false
% 1.44/1.02  
% 1.44/1.02  ------ Abstraction refinement Options
% 1.44/1.02  
% 1.44/1.02  --abstr_ref                             []
% 1.44/1.02  --abstr_ref_prep                        false
% 1.44/1.02  --abstr_ref_until_sat                   false
% 1.44/1.02  --abstr_ref_sig_restrict                funpre
% 1.44/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 1.44/1.02  --abstr_ref_under                       []
% 1.44/1.02  
% 1.44/1.02  ------ SAT Options
% 1.44/1.02  
% 1.44/1.02  --sat_mode                              false
% 1.44/1.02  --sat_fm_restart_options                ""
% 1.44/1.02  --sat_gr_def                            false
% 1.44/1.02  --sat_epr_types                         true
% 1.44/1.02  --sat_non_cyclic_types                  false
% 1.44/1.02  --sat_finite_models                     false
% 1.44/1.02  --sat_fm_lemmas                         false
% 1.44/1.02  --sat_fm_prep                           false
% 1.44/1.02  --sat_fm_uc_incr                        true
% 1.44/1.02  --sat_out_model                         small
% 1.44/1.02  --sat_out_clauses                       false
% 1.44/1.02  
% 1.44/1.02  ------ QBF Options
% 1.44/1.02  
% 1.44/1.02  --qbf_mode                              false
% 1.44/1.02  --qbf_elim_univ                         false
% 1.44/1.02  --qbf_dom_inst                          none
% 1.44/1.02  --qbf_dom_pre_inst                      false
% 1.44/1.02  --qbf_sk_in                             false
% 1.44/1.02  --qbf_pred_elim                         true
% 1.44/1.02  --qbf_split                             512
% 1.44/1.02  
% 1.44/1.02  ------ BMC1 Options
% 1.44/1.02  
% 1.44/1.02  --bmc1_incremental                      false
% 1.44/1.02  --bmc1_axioms                           reachable_all
% 1.44/1.02  --bmc1_min_bound                        0
% 1.44/1.02  --bmc1_max_bound                        -1
% 1.44/1.02  --bmc1_max_bound_default                -1
% 1.44/1.02  --bmc1_symbol_reachability              true
% 1.44/1.02  --bmc1_property_lemmas                  false
% 1.44/1.02  --bmc1_k_induction                      false
% 1.44/1.02  --bmc1_non_equiv_states                 false
% 1.44/1.02  --bmc1_deadlock                         false
% 1.44/1.02  --bmc1_ucm                              false
% 1.44/1.02  --bmc1_add_unsat_core                   none
% 1.44/1.02  --bmc1_unsat_core_children              false
% 1.44/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 1.44/1.02  --bmc1_out_stat                         full
% 1.44/1.02  --bmc1_ground_init                      false
% 1.44/1.02  --bmc1_pre_inst_next_state              false
% 1.44/1.02  --bmc1_pre_inst_state                   false
% 1.44/1.02  --bmc1_pre_inst_reach_state             false
% 1.44/1.02  --bmc1_out_unsat_core                   false
% 1.44/1.02  --bmc1_aig_witness_out                  false
% 1.44/1.02  --bmc1_verbose                          false
% 1.44/1.02  --bmc1_dump_clauses_tptp                false
% 1.44/1.02  --bmc1_dump_unsat_core_tptp             false
% 1.44/1.02  --bmc1_dump_file                        -
% 1.44/1.02  --bmc1_ucm_expand_uc_limit              128
% 1.44/1.02  --bmc1_ucm_n_expand_iterations          6
% 1.44/1.02  --bmc1_ucm_extend_mode                  1
% 1.44/1.02  --bmc1_ucm_init_mode                    2
% 1.44/1.02  --bmc1_ucm_cone_mode                    none
% 1.44/1.02  --bmc1_ucm_reduced_relation_type        0
% 1.44/1.02  --bmc1_ucm_relax_model                  4
% 1.44/1.02  --bmc1_ucm_full_tr_after_sat            true
% 1.44/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 1.44/1.02  --bmc1_ucm_layered_model                none
% 1.44/1.02  --bmc1_ucm_max_lemma_size               10
% 1.44/1.02  
% 1.44/1.02  ------ AIG Options
% 1.44/1.02  
% 1.44/1.02  --aig_mode                              false
% 1.44/1.02  
% 1.44/1.02  ------ Instantiation Options
% 1.44/1.02  
% 1.44/1.02  --instantiation_flag                    true
% 1.44/1.02  --inst_sos_flag                         false
% 1.44/1.02  --inst_sos_phase                        true
% 1.44/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.44/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.44/1.02  --inst_lit_sel_side                     none
% 1.44/1.02  --inst_solver_per_active                1400
% 1.44/1.02  --inst_solver_calls_frac                1.
% 1.44/1.02  --inst_passive_queue_type               priority_queues
% 1.44/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.44/1.02  --inst_passive_queues_freq              [25;2]
% 1.44/1.02  --inst_dismatching                      true
% 1.44/1.02  --inst_eager_unprocessed_to_passive     true
% 1.44/1.02  --inst_prop_sim_given                   true
% 1.44/1.02  --inst_prop_sim_new                     false
% 1.44/1.02  --inst_subs_new                         false
% 1.44/1.02  --inst_eq_res_simp                      false
% 1.44/1.02  --inst_subs_given                       false
% 1.44/1.02  --inst_orphan_elimination               true
% 1.44/1.02  --inst_learning_loop_flag               true
% 1.44/1.02  --inst_learning_start                   3000
% 1.44/1.02  --inst_learning_factor                  2
% 1.44/1.02  --inst_start_prop_sim_after_learn       3
% 1.44/1.02  --inst_sel_renew                        solver
% 1.44/1.02  --inst_lit_activity_flag                true
% 1.44/1.02  --inst_restr_to_given                   false
% 1.44/1.02  --inst_activity_threshold               500
% 1.44/1.02  --inst_out_proof                        true
% 1.44/1.02  
% 1.44/1.02  ------ Resolution Options
% 1.44/1.02  
% 1.44/1.02  --resolution_flag                       false
% 1.44/1.02  --res_lit_sel                           adaptive
% 1.44/1.02  --res_lit_sel_side                      none
% 1.44/1.02  --res_ordering                          kbo
% 1.44/1.02  --res_to_prop_solver                    active
% 1.44/1.02  --res_prop_simpl_new                    false
% 1.44/1.02  --res_prop_simpl_given                  true
% 1.44/1.02  --res_passive_queue_type                priority_queues
% 1.44/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.44/1.02  --res_passive_queues_freq               [15;5]
% 1.44/1.02  --res_forward_subs                      full
% 1.44/1.02  --res_backward_subs                     full
% 1.44/1.02  --res_forward_subs_resolution           true
% 1.44/1.02  --res_backward_subs_resolution          true
% 1.44/1.02  --res_orphan_elimination                true
% 1.44/1.02  --res_time_limit                        2.
% 1.44/1.02  --res_out_proof                         true
% 1.44/1.02  
% 1.44/1.02  ------ Superposition Options
% 1.44/1.02  
% 1.44/1.02  --superposition_flag                    true
% 1.44/1.02  --sup_passive_queue_type                priority_queues
% 1.44/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.44/1.02  --sup_passive_queues_freq               [8;1;4]
% 1.44/1.02  --demod_completeness_check              fast
% 1.44/1.02  --demod_use_ground                      true
% 1.44/1.02  --sup_to_prop_solver                    passive
% 1.44/1.02  --sup_prop_simpl_new                    true
% 1.44/1.02  --sup_prop_simpl_given                  true
% 1.44/1.02  --sup_fun_splitting                     false
% 1.44/1.02  --sup_smt_interval                      50000
% 1.44/1.02  
% 1.44/1.02  ------ Superposition Simplification Setup
% 1.44/1.02  
% 1.44/1.02  --sup_indices_passive                   []
% 1.44/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.44/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 1.44/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_full_bw                           [BwDemod]
% 1.44/1.02  --sup_immed_triv                        [TrivRules]
% 1.44/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.44/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_immed_bw_main                     []
% 1.44/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 1.44/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.44/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.44/1.02  
% 1.44/1.02  ------ Combination Options
% 1.44/1.02  
% 1.44/1.02  --comb_res_mult                         3
% 1.44/1.02  --comb_sup_mult                         2
% 1.44/1.02  --comb_inst_mult                        10
% 1.44/1.02  
% 1.44/1.02  ------ Debug Options
% 1.44/1.02  
% 1.44/1.02  --dbg_backtrace                         false
% 1.44/1.02  --dbg_dump_prop_clauses                 false
% 1.44/1.02  --dbg_dump_prop_clauses_file            -
% 1.44/1.02  --dbg_out_stat                          false
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  ------ Proving...
% 1.44/1.02  
% 1.44/1.02  
% 1.44/1.02  % SZS status Theorem for theBenchmark.p
% 1.44/1.02  
% 1.44/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 1.44/1.02  
% 1.44/1.02  fof(f5,axiom,(
% 1.44/1.02    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 1.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.02  
% 1.44/1.02  fof(f17,plain,(
% 1.44/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/1.02    inference(ennf_transformation,[],[f5])).
% 1.44/1.02  
% 1.44/1.02  fof(f18,plain,(
% 1.44/1.02    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/1.02    inference(flattening,[],[f17])).
% 1.44/1.02  
% 1.44/1.02  fof(f46,plain,(
% 1.44/1.02    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.02    inference(cnf_transformation,[],[f18])).
% 1.44/1.02  
% 1.44/1.02  fof(f8,conjecture,(
% 1.44/1.02    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.02  
% 1.44/1.02  fof(f9,negated_conjecture,(
% 1.44/1.02    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.44/1.02    inference(negated_conjecture,[],[f8])).
% 1.44/1.02  
% 1.44/1.02  fof(f23,plain,(
% 1.44/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.44/1.02    inference(ennf_transformation,[],[f9])).
% 1.44/1.02  
% 1.44/1.02  fof(f24,plain,(
% 1.44/1.02    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.02    inference(flattening,[],[f23])).
% 1.44/1.02  
% 1.44/1.02  fof(f30,plain,(
% 1.44/1.02    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.02    inference(nnf_transformation,[],[f24])).
% 1.44/1.02  
% 1.44/1.02  fof(f31,plain,(
% 1.44/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/1.02    inference(flattening,[],[f30])).
% 1.44/1.02  
% 1.44/1.02  fof(f33,plain,(
% 1.44/1.02    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK2),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK2),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK2),X0)) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.44/1.02    introduced(choice_axiom,[])).
% 1.44/1.02  
% 1.44/1.02  fof(f32,plain,(
% 1.44/1.02    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,X1),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),X1),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,X1),sK1)) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.44/1.02    introduced(choice_axiom,[])).
% 1.44/1.02  
% 1.44/1.02  fof(f34,plain,(
% 1.44/1.02    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.44/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f33,f32])).
% 1.44/1.02  
% 1.44/1.02  fof(f50,plain,(
% 1.44/1.02    l1_pre_topc(sK1)),
% 1.44/1.02    inference(cnf_transformation,[],[f34])).
% 1.44/1.02  
% 1.44/1.02  fof(f49,plain,(
% 1.44/1.02    ~v2_struct_0(sK1)),
% 1.44/1.02    inference(cnf_transformation,[],[f34])).
% 1.44/1.02  
% 1.44/1.02  fof(f3,axiom,(
% 1.44/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 1.44/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.02  
% 1.44/1.02  fof(f13,plain,(
% 1.44/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/1.02    inference(ennf_transformation,[],[f3])).
% 1.44/1.02  
% 1.44/1.02  fof(f14,plain,(
% 1.44/1.02    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/1.03    inference(flattening,[],[f13])).
% 1.44/1.03  
% 1.44/1.03  fof(f25,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/1.03    inference(nnf_transformation,[],[f14])).
% 1.44/1.03  
% 1.44/1.03  fof(f26,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/1.03    inference(rectify,[],[f25])).
% 1.44/1.03  
% 1.44/1.03  fof(f27,plain,(
% 1.44/1.03    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.44/1.03    introduced(choice_axiom,[])).
% 1.44/1.03  
% 1.44/1.03  fof(f28,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.44/1.03  
% 1.44/1.03  fof(f40,plain,(
% 1.44/1.03    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f28])).
% 1.44/1.03  
% 1.44/1.03  fof(f53,plain,(
% 1.44/1.03    ~v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | ~v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.44/1.03    inference(cnf_transformation,[],[f34])).
% 1.44/1.03  
% 1.44/1.03  fof(f51,plain,(
% 1.44/1.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.44/1.03    inference(cnf_transformation,[],[f34])).
% 1.44/1.03  
% 1.44/1.03  fof(f1,axiom,(
% 1.44/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.03  
% 1.44/1.03  fof(f10,plain,(
% 1.44/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/1.03    inference(ennf_transformation,[],[f1])).
% 1.44/1.03  
% 1.44/1.03  fof(f35,plain,(
% 1.44/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f10])).
% 1.44/1.03  
% 1.44/1.03  fof(f7,axiom,(
% 1.44/1.03    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 1.44/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.03  
% 1.44/1.03  fof(f21,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.03    inference(ennf_transformation,[],[f7])).
% 1.44/1.03  
% 1.44/1.03  fof(f22,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.03    inference(flattening,[],[f21])).
% 1.44/1.03  
% 1.44/1.03  fof(f48,plain,(
% 1.44/1.03    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f22])).
% 1.44/1.03  
% 1.44/1.03  fof(f2,axiom,(
% 1.44/1.03    ! [X0] : ((l1_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (~v2_struct_0(X1) => (~v1_tex_2(X1,X0) & ~v2_struct_0(X1)))))),
% 1.44/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.03  
% 1.44/1.03  fof(f11,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)))),
% 1.44/1.03    inference(ennf_transformation,[],[f2])).
% 1.44/1.03  
% 1.44/1.03  fof(f12,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : ((~v1_tex_2(X1,X0) & ~v2_struct_0(X1)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))),
% 1.44/1.03    inference(flattening,[],[f11])).
% 1.44/1.03  
% 1.44/1.03  fof(f37,plain,(
% 1.44/1.03    ( ! [X0,X1] : (~v1_tex_2(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f12])).
% 1.44/1.03  
% 1.44/1.03  fof(f44,plain,(
% 1.44/1.03    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f18])).
% 1.44/1.03  
% 1.44/1.03  fof(f41,plain,(
% 1.44/1.03    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f28])).
% 1.44/1.03  
% 1.44/1.03  fof(f4,axiom,(
% 1.44/1.03    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => (k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.44/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.44/1.03  
% 1.44/1.03  fof(f15,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/1.03    inference(ennf_transformation,[],[f4])).
% 1.44/1.03  
% 1.44/1.03  fof(f16,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (! [X2] : ((k1_tex_2(X0,X1) = X2 <=> u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/1.03    inference(flattening,[],[f15])).
% 1.44/1.03  
% 1.44/1.03  fof(f29,plain,(
% 1.44/1.03    ! [X0] : (! [X1] : (! [X2] : (((k1_tex_2(X0,X1) = X2 | u1_struct_0(X2) != k6_domain_1(u1_struct_0(X0),X1)) & (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/1.03    inference(nnf_transformation,[],[f16])).
% 1.44/1.03  
% 1.44/1.03  fof(f42,plain,(
% 1.44/1.03    ( ! [X2,X0,X1] : (u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1) | k1_tex_2(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f29])).
% 1.44/1.03  
% 1.44/1.03  fof(f55,plain,(
% 1.44/1.03    ( ! [X0,X1] : (u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1) | ~m1_pre_topc(k1_tex_2(X0,X1),X0) | ~v1_pre_topc(k1_tex_2(X0,X1)) | v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(equality_resolution,[],[f42])).
% 1.44/1.03  
% 1.44/1.03  fof(f45,plain,(
% 1.44/1.03    ( ! [X0,X1] : (v1_pre_topc(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/1.03    inference(cnf_transformation,[],[f18])).
% 1.44/1.03  
% 1.44/1.03  fof(f52,plain,(
% 1.44/1.03    v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) | v1_tex_2(k1_tex_2(sK1,sK2),sK1)),
% 1.44/1.03    inference(cnf_transformation,[],[f34])).
% 1.44/1.03  
% 1.44/1.03  cnf(c_9,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_pre_topc(X1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_17,negated_conjecture,
% 1.44/1.03      ( l1_pre_topc(sK1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_722,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_723,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.44/1.03      | v2_struct_0(sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_722]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_18,negated_conjecture,
% 1.44/1.03      ( ~ v2_struct_0(sK1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f49]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_727,plain,
% 1.44/1.03      ( m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.44/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_723,c_18]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_728,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,X0),sK1) ),
% 1.44/1.03      inference(renaming,[status(thm)],[c_727]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2358,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_728]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2670,plain,
% 1.44/1.03      ( m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_4,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.44/1.03      | v1_tex_2(X0,X1)
% 1.44/1.03      | ~ l1_pre_topc(X1)
% 1.44/1.03      | sK0(X1,X0) = u1_struct_0(X0) ),
% 1.44/1.03      inference(cnf_transformation,[],[f40]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_786,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.44/1.03      | v1_tex_2(X0,X1)
% 1.44/1.03      | sK0(X1,X0) = u1_struct_0(X0)
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_787,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.44/1.03      | v1_tex_2(X0,sK1)
% 1.44/1.03      | sK0(sK1,X0) = u1_struct_0(X0) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_786]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2356,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0_45,sK1)
% 1.44/1.03      | v1_tex_2(X0_45,sK1)
% 1.44/1.03      | sK0(sK1,X0_45) = u1_struct_0(X0_45) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_787]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2672,plain,
% 1.44/1.03      ( sK0(sK1,X0_45) = u1_struct_0(X0_45)
% 1.44/1.03      | m1_pre_topc(X0_45,sK1) != iProver_top
% 1.44/1.03      | v1_tex_2(X0_45,sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2356]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_3009,plain,
% 1.44/1.03      ( sK0(sK1,k1_tex_2(sK1,X0_44)) = u1_struct_0(k1_tex_2(sK1,X0_44))
% 1.44/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
% 1.44/1.03      inference(superposition,[status(thm)],[c_2670,c_2672]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_14,negated_conjecture,
% 1.44/1.03      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f53]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2366,negated_conjecture,
% 1.44/1.03      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2662,plain,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_16,negated_conjecture,
% 1.44/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.44/1.03      inference(cnf_transformation,[],[f51]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_0,plain,
% 1.44/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.44/1.03      inference(cnf_transformation,[],[f35]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_13,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.44/1.03      | v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_struct_0(X1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f48]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_258,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.44/1.03      | v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_pre_topc(X2)
% 1.44/1.03      | X1 != X2 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_13]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_259,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.44/1.03      | v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_pre_topc(X1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_258]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_647,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 1.44/1.03      | v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_259,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_648,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
% 1.44/1.03      | v7_struct_0(sK1)
% 1.44/1.03      | v2_struct_0(sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_647]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_652,plain,
% 1.44/1.03      ( v7_struct_0(sK1)
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
% 1.44/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_648,c_18]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_653,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0),u1_struct_0(sK1))
% 1.44/1.03      | v7_struct_0(sK1) ),
% 1.44/1.03      inference(renaming,[status(thm)],[c_652]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2360,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),X0_44),u1_struct_0(sK1))
% 1.44/1.03      | v7_struct_0(sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_653]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2404,plain,
% 1.44/1.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.44/1.03      | v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.44/1.03      | v7_struct_0(sK1) ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2360]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_1,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.44/1.03      | ~ v1_tex_2(X0,X1)
% 1.44/1.03      | ~ v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X0)
% 1.44/1.03      | ~ l1_pre_topc(X1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_801,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,X1)
% 1.44/1.03      | ~ v1_tex_2(X0,X1)
% 1.44/1.03      | ~ v7_struct_0(X1)
% 1.44/1.03      | v2_struct_0(X0)
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_802,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.44/1.03      | ~ v1_tex_2(X0,sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1)
% 1.44/1.03      | v2_struct_0(X0)
% 1.44/1.03      | v2_struct_0(sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_801]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_806,plain,
% 1.44/1.03      ( v2_struct_0(X0)
% 1.44/1.03      | ~ v7_struct_0(sK1)
% 1.44/1.03      | ~ v1_tex_2(X0,sK1)
% 1.44/1.03      | ~ m1_pre_topc(X0,sK1) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_802,c_18]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_807,plain,
% 1.44/1.03      ( ~ m1_pre_topc(X0,sK1)
% 1.44/1.03      | ~ v1_tex_2(X0,sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1)
% 1.44/1.03      | v2_struct_0(X0) ),
% 1.44/1.03      inference(renaming,[status(thm)],[c_806]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_11,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.44/1.03      | ~ l1_pre_topc(X1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_686,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_687,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | ~ v2_struct_0(k1_tex_2(sK1,X0))
% 1.44/1.03      | v2_struct_0(sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_686]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_691,plain,
% 1.44/1.03      ( ~ v2_struct_0(k1_tex_2(sK1,X0))
% 1.44/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_687,c_18]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_692,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | ~ v2_struct_0(k1_tex_2(sK1,X0)) ),
% 1.44/1.03      inference(renaming,[status(thm)],[c_691]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_915,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | ~ m1_pre_topc(X1,sK1)
% 1.44/1.03      | ~ v1_tex_2(X1,sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1)
% 1.44/1.03      | k1_tex_2(sK1,X0) != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_807,c_692]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_916,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | ~ m1_pre_topc(k1_tex_2(sK1,X0),sK1)
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,X0),sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_915]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_920,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,X0),sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_916,c_18,c_723]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2353,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,X0_44),sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_920]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2421,plain,
% 1.44/1.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.44/1.03      | ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.44/1.03      | ~ v7_struct_0(sK1) ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2353]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2448,negated_conjecture,
% 1.44/1.03      ( ~ v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_2366,c_16,c_14,c_2404,c_2421]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2450,plain,
% 1.44/1.03      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2802,plain,
% 1.44/1.03      ( v1_tex_2(k1_tex_2(sK1,sK2),sK1) != iProver_top ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_2662,c_2450]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_3136,plain,
% 1.44/1.03      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2))
% 1.44/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 1.44/1.03      inference(superposition,[status(thm)],[c_3009,c_2802]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2410,plain,
% 1.44/1.03      ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2358]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2791,plain,
% 1.44/1.03      ( ~ m1_pre_topc(k1_tex_2(sK1,X0_44),sK1)
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,X0_44),sK1)
% 1.44/1.03      | sK0(sK1,k1_tex_2(sK1,X0_44)) = u1_struct_0(k1_tex_2(sK1,X0_44)) ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2356]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2793,plain,
% 1.44/1.03      ( ~ m1_pre_topc(k1_tex_2(sK1,sK2),sK1)
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1)
% 1.44/1.03      | sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2791]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_3139,plain,
% 1.44/1.03      ( sK0(sK1,k1_tex_2(sK1,sK2)) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_3136,c_16,c_14,c_2404,c_2410,c_2421,c_2793]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_3,plain,
% 1.44/1.03      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 1.44/1.03      | ~ m1_pre_topc(X1,X0)
% 1.44/1.03      | v1_tex_2(X1,X0)
% 1.44/1.03      | ~ l1_pre_topc(X0) ),
% 1.44/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_611,plain,
% 1.44/1.03      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 1.44/1.03      | ~ m1_pre_topc(X1,X0)
% 1.44/1.03      | v1_tex_2(X1,X0)
% 1.44/1.03      | sK1 != X0 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_612,plain,
% 1.44/1.03      ( ~ v1_subset_1(sK0(sK1,X0),u1_struct_0(sK1))
% 1.44/1.03      | ~ m1_pre_topc(X0,sK1)
% 1.44/1.03      | v1_tex_2(X0,sK1) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_611]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2362,plain,
% 1.44/1.03      ( ~ v1_subset_1(sK0(sK1,X0_45),u1_struct_0(sK1))
% 1.44/1.03      | ~ m1_pre_topc(X0_45,sK1)
% 1.44/1.03      | v1_tex_2(X0_45,sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_612]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2666,plain,
% 1.44/1.03      ( v1_subset_1(sK0(sK1,X0_45),u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | m1_pre_topc(X0_45,sK1) != iProver_top
% 1.44/1.03      | v1_tex_2(X0_45,sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2362]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_3142,plain,
% 1.44/1.03      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) != iProver_top
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 1.44/1.03      inference(superposition,[status(thm)],[c_3139,c_2666]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2364,negated_conjecture,
% 1.44/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2664,plain,
% 1.44/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2364]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_8,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | ~ m1_pre_topc(k1_tex_2(X1,X0),X1)
% 1.44/1.03      | ~ v1_pre_topc(k1_tex_2(X1,X0))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | v2_struct_0(k1_tex_2(X1,X0))
% 1.44/1.03      | ~ l1_pre_topc(X1)
% 1.44/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.44/1.03      inference(cnf_transformation,[],[f55]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_10,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v1_pre_topc(k1_tex_2(X1,X0))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_pre_topc(X1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_113,plain,
% 1.44/1.03      ( v2_struct_0(X1)
% 1.44/1.03      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | ~ l1_pre_topc(X1)
% 1.44/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_8,c_11,c_10,c_9]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_114,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | ~ l1_pre_topc(X1)
% 1.44/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
% 1.44/1.03      inference(renaming,[status(thm)],[c_113]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_668,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.44/1.03      | v2_struct_0(X1)
% 1.44/1.03      | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0))
% 1.44/1.03      | sK1 != X1 ),
% 1.44/1.03      inference(resolution_lifted,[status(thm)],[c_114,c_17]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_669,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | v2_struct_0(sK1)
% 1.44/1.03      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.44/1.03      inference(unflattening,[status(thm)],[c_668]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_673,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.44/1.03      | k6_domain_1(u1_struct_0(sK1),X0) = u1_struct_0(k1_tex_2(sK1,X0)) ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_669,c_18]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2359,plain,
% 1.44/1.03      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.44/1.03      | k6_domain_1(u1_struct_0(sK1),X0_44) = u1_struct_0(k1_tex_2(sK1,X0_44)) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_673]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2669,plain,
% 1.44/1.03      ( k6_domain_1(u1_struct_0(sK1),X0_44) = u1_struct_0(k1_tex_2(sK1,X0_44))
% 1.44/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2359]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2859,plain,
% 1.44/1.03      ( k6_domain_1(u1_struct_0(sK1),sK2) = u1_struct_0(k1_tex_2(sK1,sK2)) ),
% 1.44/1.03      inference(superposition,[status(thm)],[c_2664,c_2669]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_15,negated_conjecture,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2365,negated_conjecture,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1))
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) ),
% 1.44/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2663,plain,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2365]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_22,plain,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top
% 1.44/1.03      | v1_tex_2(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2821,plain,
% 1.44/1.03      ( v1_subset_1(k6_domain_1(u1_struct_0(sK1),sK2),u1_struct_0(sK1)) = iProver_top ),
% 1.44/1.03      inference(global_propositional_subsumption,
% 1.44/1.03                [status(thm)],
% 1.44/1.03                [c_2663,c_22,c_2450]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2861,plain,
% 1.44/1.03      ( v1_subset_1(u1_struct_0(k1_tex_2(sK1,sK2)),u1_struct_0(sK1)) = iProver_top ),
% 1.44/1.03      inference(demodulation,[status(thm)],[c_2859,c_2821]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2409,plain,
% 1.44/1.03      ( m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,X0_44),sK1) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_2358]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_2411,plain,
% 1.44/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 1.44/1.03      | m1_pre_topc(k1_tex_2(sK1,sK2),sK1) = iProver_top ),
% 1.44/1.03      inference(instantiation,[status(thm)],[c_2409]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(c_21,plain,
% 1.44/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 1.44/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.44/1.03  
% 1.44/1.03  cnf(contradiction,plain,
% 1.44/1.03      ( $false ),
% 1.44/1.03      inference(minisat,[status(thm)],[c_3142,c_2861,c_2450,c_2411,c_21]) ).
% 1.44/1.03  
% 1.44/1.03  
% 1.44/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.44/1.03  
% 1.44/1.03  ------                               Statistics
% 1.44/1.03  
% 1.44/1.03  ------ General
% 1.44/1.03  
% 1.44/1.03  abstr_ref_over_cycles:                  0
% 1.44/1.03  abstr_ref_under_cycles:                 0
% 1.44/1.03  gc_basic_clause_elim:                   0
% 1.44/1.03  forced_gc_time:                         0
% 1.44/1.03  parsing_time:                           0.013
% 1.44/1.03  unif_index_cands_time:                  0.
% 1.44/1.03  unif_index_add_time:                    0.
% 1.44/1.03  orderings_time:                         0.
% 1.44/1.03  out_proof_time:                         0.013
% 1.44/1.03  total_time:                             0.111
% 1.44/1.03  num_of_symbols:                         49
% 1.44/1.03  num_of_terms:                           1666
% 1.44/1.03  
% 1.44/1.03  ------ Preprocessing
% 1.44/1.03  
% 1.44/1.03  num_of_splits:                          0
% 1.44/1.03  num_of_split_atoms:                     0
% 1.44/1.03  num_of_reused_defs:                     0
% 1.44/1.03  num_eq_ax_congr_red:                    7
% 1.44/1.03  num_of_sem_filtered_clauses:            3
% 1.44/1.03  num_of_subtypes:                        2
% 1.44/1.03  monotx_restored_types:                  0
% 1.44/1.03  sat_num_of_epr_types:                   0
% 1.44/1.03  sat_num_of_non_cyclic_types:            0
% 1.44/1.03  sat_guarded_non_collapsed_types:        0
% 1.44/1.03  num_pure_diseq_elim:                    0
% 1.44/1.03  simp_replaced_by:                       0
% 1.44/1.03  res_preprocessed:                       83
% 1.44/1.03  prep_upred:                             0
% 1.44/1.03  prep_unflattend:                        58
% 1.44/1.03  smt_new_axioms:                         0
% 1.44/1.03  pred_elim_cands:                        5
% 1.44/1.03  pred_elim:                              4
% 1.44/1.03  pred_elim_cl:                           4
% 1.44/1.03  pred_elim_cycles:                       15
% 1.44/1.03  merged_defs:                            4
% 1.44/1.03  merged_defs_ncl:                        0
% 1.44/1.03  bin_hyper_res:                          4
% 1.44/1.03  prep_cycles:                            4
% 1.44/1.03  pred_elim_time:                         0.032
% 1.44/1.03  splitting_time:                         0.
% 1.44/1.03  sem_filter_time:                        0.
% 1.44/1.03  monotx_time:                            0.
% 1.44/1.03  subtype_inf_time:                       0.
% 1.44/1.03  
% 1.44/1.03  ------ Problem properties
% 1.44/1.03  
% 1.44/1.03  clauses:                                14
% 1.44/1.03  conjectures:                            3
% 1.44/1.03  epr:                                    1
% 1.44/1.03  horn:                                   10
% 1.44/1.03  ground:                                 4
% 1.44/1.03  unary:                                  1
% 1.44/1.03  binary:                                 4
% 1.44/1.03  lits:                                   38
% 1.44/1.03  lits_eq:                                4
% 1.44/1.03  fd_pure:                                0
% 1.44/1.03  fd_pseudo:                              0
% 1.44/1.03  fd_cond:                                0
% 1.44/1.03  fd_pseudo_cond:                         0
% 1.44/1.03  ac_symbols:                             0
% 1.44/1.03  
% 1.44/1.03  ------ Propositional Solver
% 1.44/1.03  
% 1.44/1.03  prop_solver_calls:                      26
% 1.44/1.03  prop_fast_solver_calls:                 957
% 1.44/1.03  smt_solver_calls:                       0
% 1.44/1.03  smt_fast_solver_calls:                  0
% 1.44/1.03  prop_num_of_clauses:                    565
% 1.44/1.03  prop_preprocess_simplified:             2901
% 1.44/1.03  prop_fo_subsumed:                       33
% 1.44/1.03  prop_solver_time:                       0.
% 1.44/1.03  smt_solver_time:                        0.
% 1.44/1.03  smt_fast_solver_time:                   0.
% 1.44/1.03  prop_fast_solver_time:                  0.
% 1.44/1.03  prop_unsat_core_time:                   0.
% 1.44/1.03  
% 1.44/1.03  ------ QBF
% 1.44/1.03  
% 1.44/1.03  qbf_q_res:                              0
% 1.44/1.03  qbf_num_tautologies:                    0
% 1.44/1.03  qbf_prep_cycles:                        0
% 1.44/1.03  
% 1.44/1.03  ------ BMC1
% 1.44/1.03  
% 1.44/1.03  bmc1_current_bound:                     -1
% 1.44/1.03  bmc1_last_solved_bound:                 -1
% 1.44/1.03  bmc1_unsat_core_size:                   -1
% 1.44/1.03  bmc1_unsat_core_parents_size:           -1
% 1.44/1.03  bmc1_merge_next_fun:                    0
% 1.44/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.44/1.03  
% 1.44/1.03  ------ Instantiation
% 1.44/1.03  
% 1.44/1.03  inst_num_of_clauses:                    104
% 1.44/1.03  inst_num_in_passive:                    21
% 1.44/1.03  inst_num_in_active:                     66
% 1.44/1.03  inst_num_in_unprocessed:                17
% 1.44/1.03  inst_num_of_loops:                      70
% 1.44/1.03  inst_num_of_learning_restarts:          0
% 1.44/1.03  inst_num_moves_active_passive:          1
% 1.44/1.03  inst_lit_activity:                      0
% 1.44/1.03  inst_lit_activity_moves:                0
% 1.44/1.03  inst_num_tautologies:                   0
% 1.44/1.03  inst_num_prop_implied:                  0
% 1.44/1.03  inst_num_existing_simplified:           0
% 1.44/1.03  inst_num_eq_res_simplified:             0
% 1.44/1.03  inst_num_child_elim:                    0
% 1.44/1.03  inst_num_of_dismatching_blockings:      9
% 1.44/1.03  inst_num_of_non_proper_insts:           69
% 1.44/1.03  inst_num_of_duplicates:                 0
% 1.44/1.03  inst_inst_num_from_inst_to_res:         0
% 1.44/1.03  inst_dismatching_checking_time:         0.
% 1.44/1.03  
% 1.44/1.03  ------ Resolution
% 1.44/1.03  
% 1.44/1.03  res_num_of_clauses:                     0
% 1.44/1.03  res_num_in_passive:                     0
% 1.44/1.03  res_num_in_active:                      0
% 1.44/1.03  res_num_of_loops:                       87
% 1.44/1.03  res_forward_subset_subsumed:            10
% 1.44/1.03  res_backward_subset_subsumed:           0
% 1.44/1.03  res_forward_subsumed:                   0
% 1.44/1.03  res_backward_subsumed:                  0
% 1.44/1.03  res_forward_subsumption_resolution:     5
% 1.44/1.03  res_backward_subsumption_resolution:    0
% 1.44/1.03  res_clause_to_clause_subsumption:       46
% 1.44/1.03  res_orphan_elimination:                 0
% 1.44/1.03  res_tautology_del:                      23
% 1.44/1.03  res_num_eq_res_simplified:              0
% 1.44/1.03  res_num_sel_changes:                    0
% 1.44/1.03  res_moves_from_active_to_pass:          0
% 1.44/1.03  
% 1.44/1.03  ------ Superposition
% 1.44/1.03  
% 1.44/1.03  sup_time_total:                         0.
% 1.44/1.03  sup_time_generating:                    0.
% 1.44/1.03  sup_time_sim_full:                      0.
% 1.44/1.03  sup_time_sim_immed:                     0.
% 1.44/1.03  
% 1.44/1.03  sup_num_of_clauses:                     18
% 1.44/1.03  sup_num_in_active:                      13
% 1.44/1.03  sup_num_in_passive:                     5
% 1.44/1.03  sup_num_of_loops:                       13
% 1.44/1.03  sup_fw_superposition:                   2
% 1.44/1.03  sup_bw_superposition:                   3
% 1.44/1.03  sup_immediate_simplified:               0
% 1.44/1.03  sup_given_eliminated:                   0
% 1.44/1.03  comparisons_done:                       0
% 1.44/1.03  comparisons_avoided:                    0
% 1.44/1.03  
% 1.44/1.03  ------ Simplifications
% 1.44/1.03  
% 1.44/1.03  
% 1.44/1.03  sim_fw_subset_subsumed:                 0
% 1.44/1.03  sim_bw_subset_subsumed:                 0
% 1.44/1.03  sim_fw_subsumed:                        0
% 1.44/1.03  sim_bw_subsumed:                        0
% 1.44/1.03  sim_fw_subsumption_res:                 0
% 1.44/1.03  sim_bw_subsumption_res:                 0
% 1.44/1.03  sim_tautology_del:                      0
% 1.44/1.03  sim_eq_tautology_del:                   0
% 1.44/1.03  sim_eq_res_simp:                        0
% 1.44/1.03  sim_fw_demodulated:                     0
% 1.44/1.03  sim_bw_demodulated:                     1
% 1.44/1.03  sim_light_normalised:                   0
% 1.44/1.03  sim_joinable_taut:                      0
% 1.44/1.03  sim_joinable_simp:                      0
% 1.44/1.03  sim_ac_normalised:                      0
% 1.44/1.03  sim_smt_subsumption:                    0
% 1.44/1.03  
%------------------------------------------------------------------------------
