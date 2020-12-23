%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:41 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :  243 (1238 expanded)
%              Number of clauses        :  155 ( 414 expanded)
%              Number of leaves         :   26 ( 244 expanded)
%              Depth                    :   24
%              Number of atoms          :  881 (5860 expanded)
%              Number of equality atoms :  229 ( 631 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ~ v1_subset_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).

fof(f73,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f12,axiom,(
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

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f60,plain,(
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

fof(f59,plain,
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

fof(f61,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
      | v1_tex_2(k1_tex_2(sK2,sK3),sK2) )
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f60,f59])).

fof(f90,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f86,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f88,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f84,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f62,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | k6_domain_1(X0,X1) != X0
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f89,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_tex_2(k1_tex_2(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_182,plain,
    ( ~ v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_subset_1(X0,X1)
    | v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X1) ),
    inference(renaming,[status(thm)],[c_182])).

cnf(c_2763,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_subset_1(X0_46,X1_46)
    | v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(X1_46) ),
    inference(subtyping,[status(esa)],[c_183])).

cnf(c_5360,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(X0_46,u1_struct_0(sK2))
    | v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2763])).

cnf(c_6005,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,X0_46)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_6007,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6005])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_388,plain,
    ( ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_6])).

cnf(c_2762,plain,
    ( ~ v7_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | v1_zfmisc_1(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_388])).

cnf(c_3376,plain,
    ( v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2762])).

cnf(c_11,plain,
    ( v1_xboole_0(X0)
    | ~ v1_zfmisc_1(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2773,plain,
    ( v1_xboole_0(X0_46)
    | ~ v1_zfmisc_1(X0_46)
    | k6_domain_1(X0_46,sK0(X0_46)) = X0_46 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_3365,plain,
    ( k6_domain_1(X0_46,sK0(X0_46)) = X0_46
    | v1_xboole_0(X0_46) = iProver_top
    | v1_zfmisc_1(X0_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2773])).

cnf(c_3759,plain,
    ( k6_domain_1(u1_struct_0(X0_47),sK0(u1_struct_0(X0_47))) = u1_struct_0(X0_47)
    | v7_struct_0(X0_47) != iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3376,c_3365])).

cnf(c_15,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_228,plain,
    ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_758,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_228])).

cnf(c_759,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_761,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_759,c_27])).

cnf(c_762,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_761])).

cnf(c_2755,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_762])).

cnf(c_3383,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2755])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_19,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2769,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2834,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2769])).

cnf(c_2932,plain,
    ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_28,c_27,c_26,c_759,c_2834])).

cnf(c_2934,plain,
    ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2932])).

cnf(c_4808,plain,
    ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3383,c_2934])).

cnf(c_2777,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | ~ v1_subset_1(X0_46,X1_46)
    | ~ v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3361,plain,
    ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_subset_1(X0_46,X1_46) != iProver_top
    | v1_xboole_0(X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2777])).

cnf(c_4816,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4808,c_3361])).

cnf(c_29,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_30,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_87,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_89,plain,
    ( v2_struct_0(sK2) = iProver_top
    | l1_struct_0(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_91,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_93,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_struct_0(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_4841,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4816,c_29,c_30,c_89,c_93])).

cnf(c_5172,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2)
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3759,c_4841])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_88,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_92,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( v7_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_402,plain,
    ( v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_5])).

cnf(c_403,plain,
    ( v7_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_405,plain,
    ( v7_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_403])).

cnf(c_13,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_792,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_228])).

cnf(c_793,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_792])).

cnf(c_2790,plain,
    ( X0_47 != X1_47
    | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
    theory(equality)).

cnf(c_2803,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_2781,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_2811,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2781])).

cnf(c_2833,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2769])).

cnf(c_2835,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2833])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2767,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v7_struct_0(k1_tex_2(X0_47,X0_46))
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2839,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2767])).

cnf(c_2841,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2839])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_zfmisc_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1377,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X2)
    | v1_zfmisc_1(X1)
    | X1 != X2
    | k6_domain_1(X1,X0) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_zfmisc_1(X1)
    | k6_domain_1(X1,X0) != X1 ),
    inference(unflattening,[status(thm)],[c_1377])).

cnf(c_2751,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | v1_zfmisc_1(X1_46)
    | k6_domain_1(X1_46,X0_46) != X1_46 ),
    inference(subtyping,[status(esa)],[c_1378])).

cnf(c_3626,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_zfmisc_1(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2751])).

cnf(c_3627,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3626])).

cnf(c_3634,plain,
    ( ~ v7_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
    inference(instantiation,[status(thm)],[c_2762])).

cnf(c_3635,plain,
    ( v7_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3634])).

cnf(c_3637,plain,
    ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3635])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2775,plain,
    ( ~ m1_subset_1(X0_46,X1_46)
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
    | v1_xboole_0(X1_46) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3639,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2774,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
    | ~ l1_pre_topc(X1_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3642,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
    | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
    | ~ l1_pre_topc(X0_47) ),
    inference(instantiation,[status(thm)],[c_2774])).

cnf(c_3644,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3642])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2771,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
    | v1_subset_1(X0_46,X1_46)
    | X0_46 = X1_46 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_3704,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2776,plain,
    ( ~ m1_pre_topc(X0_47,X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3746,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
    | ~ l1_pre_topc(X1_47)
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_2776])).

cnf(c_3747,plain,
    ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
    | l1_pre_topc(X1_47) != iProver_top
    | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3746])).

cnf(c_3749,plain,
    ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3747])).

cnf(c_3761,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2)
    | v7_struct_0(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_3720,plain,
    ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(X0_46,u1_struct_0(sK2))
    | X0_46 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2771])).

cnf(c_3877,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
    | u1_struct_0(k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3720])).

cnf(c_3880,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3877])).

cnf(c_2785,plain,
    ( ~ v1_subset_1(X0_46,X1_46)
    | v1_subset_1(X2_46,X3_46)
    | X2_46 != X0_46
    | X3_46 != X1_46 ),
    theory(equality)).

cnf(c_3674,plain,
    ( v1_subset_1(X0_46,X1_46)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
    | X1_46 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2785])).

cnf(c_3836,plain,
    ( v1_subset_1(X0_46,u1_struct_0(sK2))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3674])).

cnf(c_4109,plain,
    ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3836])).

cnf(c_3363,plain,
    ( m1_subset_1(X0_46,X1_46) != iProver_top
    | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
    | v1_xboole_0(X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2775])).

cnf(c_3367,plain,
    ( X0_46 = X1_46
    | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
    | v1_subset_1(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2771])).

cnf(c_3941,plain,
    ( k6_domain_1(X0_46,X1_46) = X0_46
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
    | v1_xboole_0(X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_3363,c_3367])).

cnf(c_14,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_775,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK1(X1,X0) = u1_struct_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_228])).

cnf(c_776,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_775])).

cnf(c_778,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_776,c_27])).

cnf(c_779,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(renaming,[status(thm)],[c_778])).

cnf(c_2754,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(subtyping,[status(esa)],[c_779])).

cnf(c_3384,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2754])).

cnf(c_2937,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2754,c_28,c_27,c_26,c_2834])).

cnf(c_2939,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2937])).

cnf(c_4712,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3384,c_2939])).

cnf(c_4718,plain,
    ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3941,c_4712])).

cnf(c_4719,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
    | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4718])).

cnf(c_2783,plain,
    ( ~ v1_zfmisc_1(X0_46)
    | v1_zfmisc_1(X1_46)
    | X1_46 != X0_46 ),
    theory(equality)).

cnf(c_4122,plain,
    ( v1_zfmisc_1(X0_46)
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
    | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_5050,plain,
    ( v1_zfmisc_1(u1_struct_0(X0_47))
    | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
    | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
    inference(instantiation,[status(thm)],[c_4122])).

cnf(c_5052,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
    | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5050])).

cnf(c_5054,plain,
    ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
    | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5052])).

cnf(c_2782,plain,
    ( X0_46 != X1_46
    | X2_46 != X1_46
    | X2_46 = X0_46 ),
    theory(equality)).

cnf(c_3848,plain,
    ( X0_46 != X1_46
    | u1_struct_0(sK2) != X1_46
    | u1_struct_0(sK2) = X0_46 ),
    inference(instantiation,[status(thm)],[c_2782])).

cnf(c_4078,plain,
    ( X0_46 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0_46
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3848])).

cnf(c_4363,plain,
    ( u1_struct_0(X0_47) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(X0_47)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4078])).

cnf(c_5224,plain,
    ( u1_struct_0(k1_tex_2(X0_47,X0_46)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(X0_47,X0_46))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4363])).

cnf(c_5230,plain,
    ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5224])).

cnf(c_5295,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5172,c_28,c_29,c_27,c_30,c_26,c_31,c_88,c_89,c_92,c_93,c_405,c_793,c_2803,c_2811,c_2834,c_2835,c_2841,c_3627,c_3637,c_3639,c_3644,c_3704,c_3749,c_3761,c_3880,c_4109,c_4719,c_5054,c_5230])).

cnf(c_3387,plain,
    ( k6_domain_1(X0_46,X1_46) != X0_46
    | m1_subset_1(X1_46,X0_46) != iProver_top
    | v1_zfmisc_1(X0_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2751])).

cnf(c_5301,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5295,c_3387])).

cnf(c_5398,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5301,c_28,c_29,c_27,c_30,c_26,c_31,c_88,c_92,c_793,c_2803,c_2811,c_2834,c_2835,c_2841,c_3627,c_3637,c_3639,c_3644,c_3704,c_3749,c_3880,c_4109,c_4719,c_5054,c_5230])).

cnf(c_416,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_2760,plain,
    ( v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47)
    | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
    inference(subtyping,[status(esa)],[c_416])).

cnf(c_5122,plain,
    ( v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_5124,plain,
    ( v2_struct_0(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_5122])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_23])).

cnf(c_431,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
    | ~ v7_struct_0(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_2759,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
    | ~ v7_struct_0(X0_47)
    | v2_struct_0(X0_47)
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_431])).

cnf(c_3379,plain,
    ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_4957,plain,
    ( k6_domain_1(u1_struct_0(X0_47),X0_46) = u1_struct_0(X0_47)
    | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
    | v7_struct_0(X0_47) != iProver_top
    | v2_struct_0(X0_47) = iProver_top
    | l1_pre_topc(X0_47) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3941,c_3379])).

cnf(c_4959,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
    | v7_struct_0(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4957])).

cnf(c_3748,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | l1_pre_topc(k1_tex_2(sK2,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_3746])).

cnf(c_2850,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | ~ v7_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2759])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2768,plain,
    ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
    | v2_struct_0(X0_47)
    | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
    | ~ l1_pre_topc(X0_47) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2837,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v2_struct_0(k1_tex_2(sK2,sK3))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2768])).

cnf(c_16,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_169,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_8])).

cnf(c_170,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_25,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_230,plain,
    ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_25])).

cnf(c_809,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k1_tex_2(sK2,sK3) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_170,c_230])).

cnf(c_810,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_809])).

cnf(c_404,plain,
    ( v7_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_402])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6007,c_5398,c_5124,c_4959,c_3748,c_3644,c_3626,c_2850,c_2837,c_2834,c_810,c_405,c_404,c_93,c_89,c_31,c_26,c_30,c_27,c_29,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:26:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.25/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.25/0.99  
% 2.25/0.99  ------  iProver source info
% 2.25/0.99  
% 2.25/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.25/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.25/0.99  git: non_committed_changes: false
% 2.25/0.99  git: last_make_outside_of_git: false
% 2.25/0.99  
% 2.25/0.99  ------ 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options
% 2.25/0.99  
% 2.25/0.99  --out_options                           all
% 2.25/0.99  --tptp_safe_out                         true
% 2.25/0.99  --problem_path                          ""
% 2.25/0.99  --include_path                          ""
% 2.25/0.99  --clausifier                            res/vclausify_rel
% 2.25/0.99  --clausifier_options                    --mode clausify
% 2.25/0.99  --stdin                                 false
% 2.25/0.99  --stats_out                             all
% 2.25/0.99  
% 2.25/0.99  ------ General Options
% 2.25/0.99  
% 2.25/0.99  --fof                                   false
% 2.25/0.99  --time_out_real                         305.
% 2.25/0.99  --time_out_virtual                      -1.
% 2.25/0.99  --symbol_type_check                     false
% 2.25/0.99  --clausify_out                          false
% 2.25/0.99  --sig_cnt_out                           false
% 2.25/0.99  --trig_cnt_out                          false
% 2.25/0.99  --trig_cnt_out_tolerance                1.
% 2.25/0.99  --trig_cnt_out_sk_spl                   false
% 2.25/0.99  --abstr_cl_out                          false
% 2.25/0.99  
% 2.25/0.99  ------ Global Options
% 2.25/0.99  
% 2.25/0.99  --schedule                              default
% 2.25/0.99  --add_important_lit                     false
% 2.25/0.99  --prop_solver_per_cl                    1000
% 2.25/0.99  --min_unsat_core                        false
% 2.25/0.99  --soft_assumptions                      false
% 2.25/0.99  --soft_lemma_size                       3
% 2.25/0.99  --prop_impl_unit_size                   0
% 2.25/0.99  --prop_impl_unit                        []
% 2.25/0.99  --share_sel_clauses                     true
% 2.25/0.99  --reset_solvers                         false
% 2.25/0.99  --bc_imp_inh                            [conj_cone]
% 2.25/0.99  --conj_cone_tolerance                   3.
% 2.25/0.99  --extra_neg_conj                        none
% 2.25/0.99  --large_theory_mode                     true
% 2.25/0.99  --prolific_symb_bound                   200
% 2.25/0.99  --lt_threshold                          2000
% 2.25/0.99  --clause_weak_htbl                      true
% 2.25/0.99  --gc_record_bc_elim                     false
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing Options
% 2.25/0.99  
% 2.25/0.99  --preprocessing_flag                    true
% 2.25/0.99  --time_out_prep_mult                    0.1
% 2.25/0.99  --splitting_mode                        input
% 2.25/0.99  --splitting_grd                         true
% 2.25/0.99  --splitting_cvd                         false
% 2.25/0.99  --splitting_cvd_svl                     false
% 2.25/0.99  --splitting_nvd                         32
% 2.25/0.99  --sub_typing                            true
% 2.25/0.99  --prep_gs_sim                           true
% 2.25/0.99  --prep_unflatten                        true
% 2.25/0.99  --prep_res_sim                          true
% 2.25/0.99  --prep_upred                            true
% 2.25/0.99  --prep_sem_filter                       exhaustive
% 2.25/0.99  --prep_sem_filter_out                   false
% 2.25/0.99  --pred_elim                             true
% 2.25/0.99  --res_sim_input                         true
% 2.25/0.99  --eq_ax_congr_red                       true
% 2.25/0.99  --pure_diseq_elim                       true
% 2.25/0.99  --brand_transform                       false
% 2.25/0.99  --non_eq_to_eq                          false
% 2.25/0.99  --prep_def_merge                        true
% 2.25/0.99  --prep_def_merge_prop_impl              false
% 2.25/0.99  --prep_def_merge_mbd                    true
% 2.25/0.99  --prep_def_merge_tr_red                 false
% 2.25/0.99  --prep_def_merge_tr_cl                  false
% 2.25/0.99  --smt_preprocessing                     true
% 2.25/0.99  --smt_ac_axioms                         fast
% 2.25/0.99  --preprocessed_out                      false
% 2.25/0.99  --preprocessed_stats                    false
% 2.25/0.99  
% 2.25/0.99  ------ Abstraction refinement Options
% 2.25/0.99  
% 2.25/0.99  --abstr_ref                             []
% 2.25/0.99  --abstr_ref_prep                        false
% 2.25/0.99  --abstr_ref_until_sat                   false
% 2.25/0.99  --abstr_ref_sig_restrict                funpre
% 2.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.99  --abstr_ref_under                       []
% 2.25/0.99  
% 2.25/0.99  ------ SAT Options
% 2.25/0.99  
% 2.25/0.99  --sat_mode                              false
% 2.25/0.99  --sat_fm_restart_options                ""
% 2.25/0.99  --sat_gr_def                            false
% 2.25/0.99  --sat_epr_types                         true
% 2.25/0.99  --sat_non_cyclic_types                  false
% 2.25/0.99  --sat_finite_models                     false
% 2.25/0.99  --sat_fm_lemmas                         false
% 2.25/0.99  --sat_fm_prep                           false
% 2.25/0.99  --sat_fm_uc_incr                        true
% 2.25/0.99  --sat_out_model                         small
% 2.25/0.99  --sat_out_clauses                       false
% 2.25/0.99  
% 2.25/0.99  ------ QBF Options
% 2.25/0.99  
% 2.25/0.99  --qbf_mode                              false
% 2.25/0.99  --qbf_elim_univ                         false
% 2.25/0.99  --qbf_dom_inst                          none
% 2.25/0.99  --qbf_dom_pre_inst                      false
% 2.25/0.99  --qbf_sk_in                             false
% 2.25/0.99  --qbf_pred_elim                         true
% 2.25/0.99  --qbf_split                             512
% 2.25/0.99  
% 2.25/0.99  ------ BMC1 Options
% 2.25/0.99  
% 2.25/0.99  --bmc1_incremental                      false
% 2.25/0.99  --bmc1_axioms                           reachable_all
% 2.25/0.99  --bmc1_min_bound                        0
% 2.25/0.99  --bmc1_max_bound                        -1
% 2.25/0.99  --bmc1_max_bound_default                -1
% 2.25/0.99  --bmc1_symbol_reachability              true
% 2.25/0.99  --bmc1_property_lemmas                  false
% 2.25/0.99  --bmc1_k_induction                      false
% 2.25/0.99  --bmc1_non_equiv_states                 false
% 2.25/0.99  --bmc1_deadlock                         false
% 2.25/0.99  --bmc1_ucm                              false
% 2.25/0.99  --bmc1_add_unsat_core                   none
% 2.25/0.99  --bmc1_unsat_core_children              false
% 2.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.99  --bmc1_out_stat                         full
% 2.25/0.99  --bmc1_ground_init                      false
% 2.25/0.99  --bmc1_pre_inst_next_state              false
% 2.25/0.99  --bmc1_pre_inst_state                   false
% 2.25/0.99  --bmc1_pre_inst_reach_state             false
% 2.25/0.99  --bmc1_out_unsat_core                   false
% 2.25/0.99  --bmc1_aig_witness_out                  false
% 2.25/0.99  --bmc1_verbose                          false
% 2.25/0.99  --bmc1_dump_clauses_tptp                false
% 2.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.99  --bmc1_dump_file                        -
% 2.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.99  --bmc1_ucm_extend_mode                  1
% 2.25/0.99  --bmc1_ucm_init_mode                    2
% 2.25/0.99  --bmc1_ucm_cone_mode                    none
% 2.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.99  --bmc1_ucm_relax_model                  4
% 2.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.99  --bmc1_ucm_layered_model                none
% 2.25/0.99  --bmc1_ucm_max_lemma_size               10
% 2.25/0.99  
% 2.25/0.99  ------ AIG Options
% 2.25/0.99  
% 2.25/0.99  --aig_mode                              false
% 2.25/0.99  
% 2.25/0.99  ------ Instantiation Options
% 2.25/0.99  
% 2.25/0.99  --instantiation_flag                    true
% 2.25/0.99  --inst_sos_flag                         false
% 2.25/0.99  --inst_sos_phase                        true
% 2.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel_side                     num_symb
% 2.25/0.99  --inst_solver_per_active                1400
% 2.25/0.99  --inst_solver_calls_frac                1.
% 2.25/0.99  --inst_passive_queue_type               priority_queues
% 2.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.99  --inst_passive_queues_freq              [25;2]
% 2.25/0.99  --inst_dismatching                      true
% 2.25/0.99  --inst_eager_unprocessed_to_passive     true
% 2.25/0.99  --inst_prop_sim_given                   true
% 2.25/0.99  --inst_prop_sim_new                     false
% 2.25/0.99  --inst_subs_new                         false
% 2.25/0.99  --inst_eq_res_simp                      false
% 2.25/0.99  --inst_subs_given                       false
% 2.25/0.99  --inst_orphan_elimination               true
% 2.25/0.99  --inst_learning_loop_flag               true
% 2.25/0.99  --inst_learning_start                   3000
% 2.25/0.99  --inst_learning_factor                  2
% 2.25/0.99  --inst_start_prop_sim_after_learn       3
% 2.25/0.99  --inst_sel_renew                        solver
% 2.25/0.99  --inst_lit_activity_flag                true
% 2.25/0.99  --inst_restr_to_given                   false
% 2.25/0.99  --inst_activity_threshold               500
% 2.25/0.99  --inst_out_proof                        true
% 2.25/0.99  
% 2.25/0.99  ------ Resolution Options
% 2.25/0.99  
% 2.25/0.99  --resolution_flag                       true
% 2.25/0.99  --res_lit_sel                           adaptive
% 2.25/0.99  --res_lit_sel_side                      none
% 2.25/0.99  --res_ordering                          kbo
% 2.25/0.99  --res_to_prop_solver                    active
% 2.25/0.99  --res_prop_simpl_new                    false
% 2.25/0.99  --res_prop_simpl_given                  true
% 2.25/0.99  --res_passive_queue_type                priority_queues
% 2.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.99  --res_passive_queues_freq               [15;5]
% 2.25/0.99  --res_forward_subs                      full
% 2.25/0.99  --res_backward_subs                     full
% 2.25/0.99  --res_forward_subs_resolution           true
% 2.25/0.99  --res_backward_subs_resolution          true
% 2.25/0.99  --res_orphan_elimination                true
% 2.25/0.99  --res_time_limit                        2.
% 2.25/0.99  --res_out_proof                         true
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Options
% 2.25/0.99  
% 2.25/0.99  --superposition_flag                    true
% 2.25/0.99  --sup_passive_queue_type                priority_queues
% 2.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.99  --demod_completeness_check              fast
% 2.25/0.99  --demod_use_ground                      true
% 2.25/0.99  --sup_to_prop_solver                    passive
% 2.25/0.99  --sup_prop_simpl_new                    true
% 2.25/0.99  --sup_prop_simpl_given                  true
% 2.25/0.99  --sup_fun_splitting                     false
% 2.25/0.99  --sup_smt_interval                      50000
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Simplification Setup
% 2.25/0.99  
% 2.25/0.99  --sup_indices_passive                   []
% 2.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_full_bw                           [BwDemod]
% 2.25/0.99  --sup_immed_triv                        [TrivRules]
% 2.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_immed_bw_main                     []
% 2.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  
% 2.25/0.99  ------ Combination Options
% 2.25/0.99  
% 2.25/0.99  --comb_res_mult                         3
% 2.25/0.99  --comb_sup_mult                         2
% 2.25/0.99  --comb_inst_mult                        10
% 2.25/0.99  
% 2.25/0.99  ------ Debug Options
% 2.25/0.99  
% 2.25/0.99  --dbg_backtrace                         false
% 2.25/0.99  --dbg_dump_prop_clauses                 false
% 2.25/0.99  --dbg_dump_prop_clauses_file            -
% 2.25/0.99  --dbg_out_stat                          false
% 2.25/0.99  ------ Parsing...
% 2.25/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.25/0.99  ------ Proving...
% 2.25/0.99  ------ Problem Properties 
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  clauses                                 28
% 2.25/0.99  conjectures                             3
% 2.25/0.99  EPR                                     4
% 2.25/0.99  Horn                                    19
% 2.25/0.99  unary                                   3
% 2.25/0.99  binary                                  2
% 2.25/0.99  lits                                    85
% 2.25/0.99  lits eq                                 5
% 2.25/0.99  fd_pure                                 0
% 2.25/0.99  fd_pseudo                               0
% 2.25/0.99  fd_cond                                 0
% 2.25/0.99  fd_pseudo_cond                          1
% 2.25/0.99  AC symbols                              0
% 2.25/0.99  
% 2.25/0.99  ------ Schedule dynamic 5 is on 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  ------ 
% 2.25/0.99  Current options:
% 2.25/0.99  ------ 
% 2.25/0.99  
% 2.25/0.99  ------ Input Options
% 2.25/0.99  
% 2.25/0.99  --out_options                           all
% 2.25/0.99  --tptp_safe_out                         true
% 2.25/0.99  --problem_path                          ""
% 2.25/0.99  --include_path                          ""
% 2.25/0.99  --clausifier                            res/vclausify_rel
% 2.25/0.99  --clausifier_options                    --mode clausify
% 2.25/0.99  --stdin                                 false
% 2.25/0.99  --stats_out                             all
% 2.25/0.99  
% 2.25/0.99  ------ General Options
% 2.25/0.99  
% 2.25/0.99  --fof                                   false
% 2.25/0.99  --time_out_real                         305.
% 2.25/0.99  --time_out_virtual                      -1.
% 2.25/0.99  --symbol_type_check                     false
% 2.25/0.99  --clausify_out                          false
% 2.25/0.99  --sig_cnt_out                           false
% 2.25/0.99  --trig_cnt_out                          false
% 2.25/0.99  --trig_cnt_out_tolerance                1.
% 2.25/0.99  --trig_cnt_out_sk_spl                   false
% 2.25/0.99  --abstr_cl_out                          false
% 2.25/0.99  
% 2.25/0.99  ------ Global Options
% 2.25/0.99  
% 2.25/0.99  --schedule                              default
% 2.25/0.99  --add_important_lit                     false
% 2.25/0.99  --prop_solver_per_cl                    1000
% 2.25/0.99  --min_unsat_core                        false
% 2.25/0.99  --soft_assumptions                      false
% 2.25/0.99  --soft_lemma_size                       3
% 2.25/0.99  --prop_impl_unit_size                   0
% 2.25/0.99  --prop_impl_unit                        []
% 2.25/0.99  --share_sel_clauses                     true
% 2.25/0.99  --reset_solvers                         false
% 2.25/0.99  --bc_imp_inh                            [conj_cone]
% 2.25/0.99  --conj_cone_tolerance                   3.
% 2.25/0.99  --extra_neg_conj                        none
% 2.25/0.99  --large_theory_mode                     true
% 2.25/0.99  --prolific_symb_bound                   200
% 2.25/0.99  --lt_threshold                          2000
% 2.25/0.99  --clause_weak_htbl                      true
% 2.25/0.99  --gc_record_bc_elim                     false
% 2.25/0.99  
% 2.25/0.99  ------ Preprocessing Options
% 2.25/0.99  
% 2.25/0.99  --preprocessing_flag                    true
% 2.25/0.99  --time_out_prep_mult                    0.1
% 2.25/0.99  --splitting_mode                        input
% 2.25/0.99  --splitting_grd                         true
% 2.25/0.99  --splitting_cvd                         false
% 2.25/0.99  --splitting_cvd_svl                     false
% 2.25/0.99  --splitting_nvd                         32
% 2.25/0.99  --sub_typing                            true
% 2.25/0.99  --prep_gs_sim                           true
% 2.25/0.99  --prep_unflatten                        true
% 2.25/0.99  --prep_res_sim                          true
% 2.25/0.99  --prep_upred                            true
% 2.25/0.99  --prep_sem_filter                       exhaustive
% 2.25/0.99  --prep_sem_filter_out                   false
% 2.25/0.99  --pred_elim                             true
% 2.25/0.99  --res_sim_input                         true
% 2.25/0.99  --eq_ax_congr_red                       true
% 2.25/0.99  --pure_diseq_elim                       true
% 2.25/0.99  --brand_transform                       false
% 2.25/0.99  --non_eq_to_eq                          false
% 2.25/0.99  --prep_def_merge                        true
% 2.25/0.99  --prep_def_merge_prop_impl              false
% 2.25/0.99  --prep_def_merge_mbd                    true
% 2.25/0.99  --prep_def_merge_tr_red                 false
% 2.25/0.99  --prep_def_merge_tr_cl                  false
% 2.25/0.99  --smt_preprocessing                     true
% 2.25/0.99  --smt_ac_axioms                         fast
% 2.25/0.99  --preprocessed_out                      false
% 2.25/0.99  --preprocessed_stats                    false
% 2.25/0.99  
% 2.25/0.99  ------ Abstraction refinement Options
% 2.25/0.99  
% 2.25/0.99  --abstr_ref                             []
% 2.25/0.99  --abstr_ref_prep                        false
% 2.25/0.99  --abstr_ref_until_sat                   false
% 2.25/0.99  --abstr_ref_sig_restrict                funpre
% 2.25/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.25/0.99  --abstr_ref_under                       []
% 2.25/0.99  
% 2.25/0.99  ------ SAT Options
% 2.25/0.99  
% 2.25/0.99  --sat_mode                              false
% 2.25/0.99  --sat_fm_restart_options                ""
% 2.25/0.99  --sat_gr_def                            false
% 2.25/0.99  --sat_epr_types                         true
% 2.25/0.99  --sat_non_cyclic_types                  false
% 2.25/0.99  --sat_finite_models                     false
% 2.25/0.99  --sat_fm_lemmas                         false
% 2.25/0.99  --sat_fm_prep                           false
% 2.25/0.99  --sat_fm_uc_incr                        true
% 2.25/0.99  --sat_out_model                         small
% 2.25/0.99  --sat_out_clauses                       false
% 2.25/0.99  
% 2.25/0.99  ------ QBF Options
% 2.25/0.99  
% 2.25/0.99  --qbf_mode                              false
% 2.25/0.99  --qbf_elim_univ                         false
% 2.25/0.99  --qbf_dom_inst                          none
% 2.25/0.99  --qbf_dom_pre_inst                      false
% 2.25/0.99  --qbf_sk_in                             false
% 2.25/0.99  --qbf_pred_elim                         true
% 2.25/0.99  --qbf_split                             512
% 2.25/0.99  
% 2.25/0.99  ------ BMC1 Options
% 2.25/0.99  
% 2.25/0.99  --bmc1_incremental                      false
% 2.25/0.99  --bmc1_axioms                           reachable_all
% 2.25/0.99  --bmc1_min_bound                        0
% 2.25/0.99  --bmc1_max_bound                        -1
% 2.25/0.99  --bmc1_max_bound_default                -1
% 2.25/0.99  --bmc1_symbol_reachability              true
% 2.25/0.99  --bmc1_property_lemmas                  false
% 2.25/0.99  --bmc1_k_induction                      false
% 2.25/0.99  --bmc1_non_equiv_states                 false
% 2.25/0.99  --bmc1_deadlock                         false
% 2.25/0.99  --bmc1_ucm                              false
% 2.25/0.99  --bmc1_add_unsat_core                   none
% 2.25/0.99  --bmc1_unsat_core_children              false
% 2.25/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.25/0.99  --bmc1_out_stat                         full
% 2.25/0.99  --bmc1_ground_init                      false
% 2.25/0.99  --bmc1_pre_inst_next_state              false
% 2.25/0.99  --bmc1_pre_inst_state                   false
% 2.25/0.99  --bmc1_pre_inst_reach_state             false
% 2.25/0.99  --bmc1_out_unsat_core                   false
% 2.25/0.99  --bmc1_aig_witness_out                  false
% 2.25/0.99  --bmc1_verbose                          false
% 2.25/0.99  --bmc1_dump_clauses_tptp                false
% 2.25/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.25/0.99  --bmc1_dump_file                        -
% 2.25/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.25/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.25/0.99  --bmc1_ucm_extend_mode                  1
% 2.25/0.99  --bmc1_ucm_init_mode                    2
% 2.25/0.99  --bmc1_ucm_cone_mode                    none
% 2.25/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.25/0.99  --bmc1_ucm_relax_model                  4
% 2.25/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.25/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.25/0.99  --bmc1_ucm_layered_model                none
% 2.25/0.99  --bmc1_ucm_max_lemma_size               10
% 2.25/0.99  
% 2.25/0.99  ------ AIG Options
% 2.25/0.99  
% 2.25/0.99  --aig_mode                              false
% 2.25/0.99  
% 2.25/0.99  ------ Instantiation Options
% 2.25/0.99  
% 2.25/0.99  --instantiation_flag                    true
% 2.25/0.99  --inst_sos_flag                         false
% 2.25/0.99  --inst_sos_phase                        true
% 2.25/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.25/0.99  --inst_lit_sel_side                     none
% 2.25/0.99  --inst_solver_per_active                1400
% 2.25/0.99  --inst_solver_calls_frac                1.
% 2.25/0.99  --inst_passive_queue_type               priority_queues
% 2.25/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.25/0.99  --inst_passive_queues_freq              [25;2]
% 2.25/0.99  --inst_dismatching                      true
% 2.25/0.99  --inst_eager_unprocessed_to_passive     true
% 2.25/0.99  --inst_prop_sim_given                   true
% 2.25/0.99  --inst_prop_sim_new                     false
% 2.25/0.99  --inst_subs_new                         false
% 2.25/0.99  --inst_eq_res_simp                      false
% 2.25/0.99  --inst_subs_given                       false
% 2.25/0.99  --inst_orphan_elimination               true
% 2.25/0.99  --inst_learning_loop_flag               true
% 2.25/0.99  --inst_learning_start                   3000
% 2.25/0.99  --inst_learning_factor                  2
% 2.25/0.99  --inst_start_prop_sim_after_learn       3
% 2.25/0.99  --inst_sel_renew                        solver
% 2.25/0.99  --inst_lit_activity_flag                true
% 2.25/0.99  --inst_restr_to_given                   false
% 2.25/0.99  --inst_activity_threshold               500
% 2.25/0.99  --inst_out_proof                        true
% 2.25/0.99  
% 2.25/0.99  ------ Resolution Options
% 2.25/0.99  
% 2.25/0.99  --resolution_flag                       false
% 2.25/0.99  --res_lit_sel                           adaptive
% 2.25/0.99  --res_lit_sel_side                      none
% 2.25/0.99  --res_ordering                          kbo
% 2.25/0.99  --res_to_prop_solver                    active
% 2.25/0.99  --res_prop_simpl_new                    false
% 2.25/0.99  --res_prop_simpl_given                  true
% 2.25/0.99  --res_passive_queue_type                priority_queues
% 2.25/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.25/0.99  --res_passive_queues_freq               [15;5]
% 2.25/0.99  --res_forward_subs                      full
% 2.25/0.99  --res_backward_subs                     full
% 2.25/0.99  --res_forward_subs_resolution           true
% 2.25/0.99  --res_backward_subs_resolution          true
% 2.25/0.99  --res_orphan_elimination                true
% 2.25/0.99  --res_time_limit                        2.
% 2.25/0.99  --res_out_proof                         true
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Options
% 2.25/0.99  
% 2.25/0.99  --superposition_flag                    true
% 2.25/0.99  --sup_passive_queue_type                priority_queues
% 2.25/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.25/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.25/0.99  --demod_completeness_check              fast
% 2.25/0.99  --demod_use_ground                      true
% 2.25/0.99  --sup_to_prop_solver                    passive
% 2.25/0.99  --sup_prop_simpl_new                    true
% 2.25/0.99  --sup_prop_simpl_given                  true
% 2.25/0.99  --sup_fun_splitting                     false
% 2.25/0.99  --sup_smt_interval                      50000
% 2.25/0.99  
% 2.25/0.99  ------ Superposition Simplification Setup
% 2.25/0.99  
% 2.25/0.99  --sup_indices_passive                   []
% 2.25/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.25/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.25/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_full_bw                           [BwDemod]
% 2.25/0.99  --sup_immed_triv                        [TrivRules]
% 2.25/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.25/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_immed_bw_main                     []
% 2.25/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.25/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.25/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.25/0.99  
% 2.25/0.99  ------ Combination Options
% 2.25/0.99  
% 2.25/0.99  --comb_res_mult                         3
% 2.25/0.99  --comb_sup_mult                         2
% 2.25/0.99  --comb_inst_mult                        10
% 2.25/0.99  
% 2.25/0.99  ------ Debug Options
% 2.25/0.99  
% 2.25/0.99  --dbg_backtrace                         false
% 2.25/0.99  --dbg_dump_prop_clauses                 false
% 2.25/0.99  --dbg_dump_prop_clauses_file            -
% 2.25/0.99  --dbg_out_stat                          false
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  ------ Proving...
% 2.25/0.99  
% 2.25/0.99  
% 2.25/0.99  % SZS status Theorem for theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.25/0.99  
% 2.25/0.99  fof(f10,axiom,(
% 2.25/0.99    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f34,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f10])).
% 2.25/0.99  
% 2.25/0.99  fof(f35,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 2.25/0.99    inference(flattening,[],[f34])).
% 2.25/0.99  
% 2.25/0.99  fof(f71,plain,(
% 2.25/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f35])).
% 2.25/0.99  
% 2.25/0.99  fof(f2,axiom,(
% 2.25/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~v1_subset_1(X1,X0)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f22,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f2])).
% 2.25/0.99  
% 2.25/0.99  fof(f63,plain,(
% 2.25/0.99    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f22])).
% 2.25/0.99  
% 2.25/0.99  fof(f3,axiom,(
% 2.25/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f23,plain,(
% 2.25/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f3])).
% 2.25/0.99  
% 2.25/0.99  fof(f64,plain,(
% 2.25/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f23])).
% 2.25/0.99  
% 2.25/0.99  fof(f7,axiom,(
% 2.25/0.99    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f29,plain,(
% 2.25/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f7])).
% 2.25/0.99  
% 2.25/0.99  fof(f30,plain,(
% 2.25/0.99    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f29])).
% 2.25/0.99  
% 2.25/0.99  fof(f68,plain,(
% 2.25/0.99    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f30])).
% 2.25/0.99  
% 2.25/0.99  fof(f11,axiom,(
% 2.25/0.99    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f36,plain,(
% 2.25/0.99    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f11])).
% 2.25/0.99  
% 2.25/0.99  fof(f48,plain,(
% 2.25/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.25/0.99    inference(nnf_transformation,[],[f36])).
% 2.25/0.99  
% 2.25/0.99  fof(f49,plain,(
% 2.25/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.25/0.99    inference(rectify,[],[f48])).
% 2.25/0.99  
% 2.25/0.99  fof(f50,plain,(
% 2.25/0.99    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f51,plain,(
% 2.25/0.99    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 2.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f49,f50])).
% 2.25/0.99  
% 2.25/0.99  fof(f73,plain,(
% 2.25/0.99    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f51])).
% 2.25/0.99  
% 2.25/0.99  fof(f12,axiom,(
% 2.25/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f37,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f12])).
% 2.25/0.99  
% 2.25/0.99  fof(f38,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(flattening,[],[f37])).
% 2.25/0.99  
% 2.25/0.99  fof(f52,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(nnf_transformation,[],[f38])).
% 2.25/0.99  
% 2.25/0.99  fof(f53,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(rectify,[],[f52])).
% 2.25/0.99  
% 2.25/0.99  fof(f54,plain,(
% 2.25/0.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f55,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f53,f54])).
% 2.25/0.99  
% 2.25/0.99  fof(f76,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f55])).
% 2.25/0.99  
% 2.25/0.99  fof(f17,conjecture,(
% 2.25/0.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f18,negated_conjecture,(
% 2.25/0.99    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.25/0.99    inference(negated_conjecture,[],[f17])).
% 2.25/0.99  
% 2.25/0.99  fof(f46,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f18])).
% 2.25/0.99  
% 2.25/0.99  fof(f47,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f46])).
% 2.25/0.99  
% 2.25/0.99  fof(f57,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.25/0.99    inference(nnf_transformation,[],[f47])).
% 2.25/0.99  
% 2.25/0.99  fof(f58,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f57])).
% 2.25/0.99  
% 2.25/0.99  fof(f60,plain,(
% 2.25/0.99    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK3),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK3),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK3),X0)) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f59,plain,(
% 2.25/0.99    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,X1),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),X1),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,X1),sK2)) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.25/0.99    introduced(choice_axiom,[])).
% 2.25/0.99  
% 2.25/0.99  fof(f61,plain,(
% 2.25/0.99    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.25/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f58,f60,f59])).
% 2.25/0.99  
% 2.25/0.99  fof(f90,plain,(
% 2.25/0.99    ~v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | ~v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f61])).
% 2.25/0.99  
% 2.25/0.99  fof(f87,plain,(
% 2.25/0.99    l1_pre_topc(sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f61])).
% 2.25/0.99  
% 2.25/0.99  fof(f86,plain,(
% 2.25/0.99    ~v2_struct_0(sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f61])).
% 2.25/0.99  
% 2.25/0.99  fof(f88,plain,(
% 2.25/0.99    m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.25/0.99    inference(cnf_transformation,[],[f61])).
% 2.25/0.99  
% 2.25/0.99  fof(f14,axiom,(
% 2.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f19,plain,(
% 2.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.25/0.99    inference(pure_predicate_removal,[],[f14])).
% 2.25/0.99  
% 2.25/0.99  fof(f40,plain,(
% 2.25/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f19])).
% 2.25/0.99  
% 2.25/0.99  fof(f41,plain,(
% 2.25/0.99    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f40])).
% 2.25/0.99  
% 2.25/0.99  fof(f82,plain,(
% 2.25/0.99    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f41])).
% 2.25/0.99  
% 2.25/0.99  fof(f5,axiom,(
% 2.25/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f25,plain,(
% 2.25/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f5])).
% 2.25/0.99  
% 2.25/0.99  fof(f26,plain,(
% 2.25/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f25])).
% 2.25/0.99  
% 2.25/0.99  fof(f66,plain,(
% 2.25/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f26])).
% 2.25/0.99  
% 2.25/0.99  fof(f6,axiom,(
% 2.25/0.99    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f27,plain,(
% 2.25/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f6])).
% 2.25/0.99  
% 2.25/0.99  fof(f28,plain,(
% 2.25/0.99    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f27])).
% 2.25/0.99  
% 2.25/0.99  fof(f67,plain,(
% 2.25/0.99    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f28])).
% 2.25/0.99  
% 2.25/0.99  fof(f78,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f55])).
% 2.25/0.99  
% 2.25/0.99  fof(f15,axiom,(
% 2.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f20,plain,(
% 2.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 2.25/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.25/0.99  
% 2.25/0.99  fof(f42,plain,(
% 2.25/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f20])).
% 2.25/0.99  
% 2.25/0.99  fof(f43,plain,(
% 2.25/0.99    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f42])).
% 2.25/0.99  
% 2.25/0.99  fof(f84,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f43])).
% 2.25/0.99  
% 2.25/0.99  fof(f1,axiom,(
% 2.25/0.99    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f21,plain,(
% 2.25/0.99    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f1])).
% 2.25/0.99  
% 2.25/0.99  fof(f62,plain,(
% 2.25/0.99    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f21])).
% 2.25/0.99  
% 2.25/0.99  fof(f74,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_zfmisc_1(X0) | k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f51])).
% 2.25/0.99  
% 2.25/0.99  fof(f8,axiom,(
% 2.25/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f31,plain,(
% 2.25/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f8])).
% 2.25/0.99  
% 2.25/0.99  fof(f32,plain,(
% 2.25/0.99    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.25/0.99    inference(flattening,[],[f31])).
% 2.25/0.99  
% 2.25/0.99  fof(f69,plain,(
% 2.25/0.99    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f32])).
% 2.25/0.99  
% 2.25/0.99  fof(f9,axiom,(
% 2.25/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f33,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f9])).
% 2.25/0.99  
% 2.25/0.99  fof(f70,plain,(
% 2.25/0.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f33])).
% 2.25/0.99  
% 2.25/0.99  fof(f13,axiom,(
% 2.25/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f39,plain,(
% 2.25/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f13])).
% 2.25/0.99  
% 2.25/0.99  fof(f56,plain,(
% 2.25/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.25/0.99    inference(nnf_transformation,[],[f39])).
% 2.25/0.99  
% 2.25/0.99  fof(f80,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.25/0.99    inference(cnf_transformation,[],[f56])).
% 2.25/0.99  
% 2.25/0.99  fof(f4,axiom,(
% 2.25/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f24,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.25/0.99    inference(ennf_transformation,[],[f4])).
% 2.25/0.99  
% 2.25/0.99  fof(f65,plain,(
% 2.25/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f24])).
% 2.25/0.99  
% 2.25/0.99  fof(f77,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f55])).
% 2.25/0.99  
% 2.25/0.99  fof(f16,axiom,(
% 2.25/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 2.25/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.25/0.99  
% 2.25/0.99  fof(f44,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.25/0.99    inference(ennf_transformation,[],[f16])).
% 2.25/0.99  
% 2.25/0.99  fof(f45,plain,(
% 2.25/0.99    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.25/0.99    inference(flattening,[],[f44])).
% 2.25/0.99  
% 2.25/0.99  fof(f85,plain,(
% 2.25/0.99    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f45])).
% 2.25/0.99  
% 2.25/0.99  fof(f83,plain,(
% 2.25/0.99    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f43])).
% 2.25/0.99  
% 2.25/0.99  fof(f75,plain,(
% 2.25/0.99    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(cnf_transformation,[],[f55])).
% 2.25/0.99  
% 2.25/0.99  fof(f91,plain,(
% 2.25/0.99    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.25/0.99    inference(equality_resolution,[],[f75])).
% 2.25/0.99  
% 2.25/0.99  fof(f89,plain,(
% 2.25/0.99    v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) | v1_tex_2(k1_tex_2(sK2,sK3),sK2)),
% 2.25/0.99    inference(cnf_transformation,[],[f61])).
% 2.25/0.99  
% 2.25/0.99  cnf(c_9,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | ~ v1_subset_1(X0,X1)
% 2.25/0.99      | v1_xboole_0(X1)
% 2.25/0.99      | v1_xboole_0(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | ~ v1_subset_1(X0,X1)
% 2.25/0.99      | ~ v1_xboole_0(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_182,plain,
% 2.25/0.99      ( ~ v1_subset_1(X0,X1)
% 2.25/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | v1_xboole_0(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(X1) ),
% 2.25/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_183,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | ~ v1_subset_1(X0,X1)
% 2.25/0.99      | v1_xboole_0(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(X1) ),
% 2.25/0.99      inference(renaming,[status(thm)],[c_182]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2763,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.25/0.99      | ~ v1_subset_1(X0_46,X1_46)
% 2.25/0.99      | v1_xboole_0(X0_46)
% 2.25/0.99      | ~ v1_zfmisc_1(X1_46) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_183]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5360,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.25/0.99      | v1_xboole_0(X0_46)
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2763]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_6005,plain,
% 2.25/0.99      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 2.25/0.99      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,X0_46)))
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_5360]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_6007,plain,
% 2.25/0.99      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3)))
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_6005]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2,plain,
% 2.25/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_6,plain,
% 2.25/0.99      ( ~ v7_struct_0(X0)
% 2.25/0.99      | ~ l1_struct_0(X0)
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_388,plain,
% 2.25/0.99      ( ~ v7_struct_0(X0)
% 2.25/0.99      | ~ l1_pre_topc(X0)
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.25/0.99      inference(resolution,[status(thm)],[c_2,c_6]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2762,plain,
% 2.25/0.99      ( ~ v7_struct_0(X0_47)
% 2.25/0.99      | ~ l1_pre_topc(X0_47)
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0_47)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_388]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3376,plain,
% 2.25/0.99      ( v7_struct_0(X0_47) != iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2762]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_11,plain,
% 2.25/0.99      ( v1_xboole_0(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(X0)
% 2.25/0.99      | k6_domain_1(X0,sK0(X0)) = X0 ),
% 2.25/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2773,plain,
% 2.25/0.99      ( v1_xboole_0(X0_46)
% 2.25/0.99      | ~ v1_zfmisc_1(X0_46)
% 2.25/0.99      | k6_domain_1(X0_46,sK0(X0_46)) = X0_46 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3365,plain,
% 2.25/0.99      ( k6_domain_1(X0_46,sK0(X0_46)) = X0_46
% 2.25/0.99      | v1_xboole_0(X0_46) = iProver_top
% 2.25/0.99      | v1_zfmisc_1(X0_46) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2773]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3759,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(X0_47),sK0(u1_struct_0(X0_47))) = u1_struct_0(X0_47)
% 2.25/0.99      | v7_struct_0(X0_47) != iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_3376,c_3365]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_15,plain,
% 2.25/0.99      ( v1_tex_2(X0,X1)
% 2.25/0.99      | ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_24,negated_conjecture,
% 2.25/0.99      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_228,plain,
% 2.25/0.99      ( ~ v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_758,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(X1)
% 2.25/0.99      | k1_tex_2(sK2,sK3) != X0
% 2.25/0.99      | sK2 != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_228]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_759,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_758]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_27,negated_conjecture,
% 2.25/0.99      ( l1_pre_topc(sK2) ),
% 2.25/0.99      inference(cnf_transformation,[],[f87]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_761,plain,
% 2.25/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_759,c_27]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_762,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/0.99      inference(renaming,[status(thm)],[c_761]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2755,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_762]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3383,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.25/0.99      | m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2755]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_28,negated_conjecture,
% 2.25/0.99      ( ~ v2_struct_0(sK2) ),
% 2.25/0.99      inference(cnf_transformation,[],[f86]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_26,negated_conjecture,
% 2.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_19,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 2.25/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.25/0.99      | v2_struct_0(X0)
% 2.25/0.99      | ~ l1_pre_topc(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2769,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.25/0.99      | ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.25/0.99      | v2_struct_0(X0_47)
% 2.25/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_19]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2834,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/0.99      | v2_struct_0(sK2)
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2769]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2932,plain,
% 2.25/0.99      ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_2755,c_28,c_27,c_26,c_759,c_2834]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2934,plain,
% 2.25/0.99      ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2932]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4808,plain,
% 2.25/0.99      ( m1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_3383,c_2934]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2777,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.25/0.99      | ~ v1_subset_1(X0_46,X1_46)
% 2.25/0.99      | ~ v1_xboole_0(X1_46) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3361,plain,
% 2.25/0.99      ( m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.25/0.99      | v1_subset_1(X0_46,X1_46) != iProver_top
% 2.25/0.99      | v1_xboole_0(X1_46) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2777]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4816,plain,
% 2.25/0.99      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_4808,c_3361]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_29,plain,
% 2.25/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_30,plain,
% 2.25/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4,plain,
% 2.25/0.99      ( v2_struct_0(X0)
% 2.25/0.99      | ~ l1_struct_0(X0)
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_87,plain,
% 2.25/0.99      ( v2_struct_0(X0) = iProver_top
% 2.25/0.99      | l1_struct_0(X0) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_89,plain,
% 2.25/0.99      ( v2_struct_0(sK2) = iProver_top
% 2.25/0.99      | l1_struct_0(sK2) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_87]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_91,plain,
% 2.25/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_93,plain,
% 2.25/0.99      ( l1_pre_topc(sK2) != iProver_top
% 2.25/0.99      | l1_struct_0(sK2) = iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_91]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4841,plain,
% 2.25/0.99      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_4816,c_29,c_30,c_89,c_93]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5172,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2)
% 2.25/0.99      | v7_struct_0(sK2) != iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_3759,c_4841]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_31,plain,
% 2.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_88,plain,
% 2.25/0.99      ( v2_struct_0(sK2)
% 2.25/0.99      | ~ l1_struct_0(sK2)
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_92,plain,
% 2.25/0.99      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5,plain,
% 2.25/0.99      ( v7_struct_0(X0)
% 2.25/0.99      | ~ l1_struct_0(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.25/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_402,plain,
% 2.25/0.99      ( v7_struct_0(X0)
% 2.25/0.99      | ~ l1_pre_topc(X0)
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(X0)) ),
% 2.25/0.99      inference(resolution,[status(thm)],[c_2,c_5]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_403,plain,
% 2.25/0.99      ( v7_struct_0(X0) = iProver_top
% 2.25/0.99      | l1_pre_topc(X0) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_405,plain,
% 2.25/0.99      ( v7_struct_0(sK2) = iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_403]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_13,plain,
% 2.25/0.99      ( v1_tex_2(X0,X1)
% 2.25/0.99      | ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_792,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(X1)
% 2.25/0.99      | k1_tex_2(sK2,sK3) != X0
% 2.25/0.99      | sK2 != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_228]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_793,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_792]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2790,plain,
% 2.25/0.99      ( X0_47 != X1_47 | u1_struct_0(X0_47) = u1_struct_0(X1_47) ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2803,plain,
% 2.25/0.99      ( sK2 != sK2 | u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2790]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2781,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2811,plain,
% 2.25/0.99      ( sK2 = sK2 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2781]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2833,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47) = iProver_top
% 2.25/0.99      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.25/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2769]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2835,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) = iProver_top
% 2.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v2_struct_0(sK2) = iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2833]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_21,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/0.99      | v7_struct_0(k1_tex_2(X1,X0))
% 2.25/0.99      | v2_struct_0(X1)
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2767,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.25/0.99      | v7_struct_0(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | v2_struct_0(X0_47)
% 2.25/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2839,plain,
% 2.25/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.25/0.99      | v7_struct_0(k1_tex_2(X0_47,X0_46)) = iProver_top
% 2.25/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2767]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2841,plain,
% 2.25/0.99      ( m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v7_struct_0(k1_tex_2(sK2,sK3)) = iProver_top
% 2.25/0.99      | v2_struct_0(sK2) = iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2839]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_0,plain,
% 2.25/0.99      ( ~ v1_xboole_0(X0) | v1_zfmisc_1(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_10,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,X1)
% 2.25/0.99      | v1_xboole_0(X1)
% 2.25/0.99      | v1_zfmisc_1(X1)
% 2.25/0.99      | k6_domain_1(X1,X0) != X1 ),
% 2.25/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1377,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,X1)
% 2.25/0.99      | v1_zfmisc_1(X2)
% 2.25/0.99      | v1_zfmisc_1(X1)
% 2.25/0.99      | X1 != X2
% 2.25/0.99      | k6_domain_1(X1,X0) != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_1378,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,X1)
% 2.25/0.99      | v1_zfmisc_1(X1)
% 2.25/0.99      | k6_domain_1(X1,X0) != X1 ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_1377]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2751,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,X1_46)
% 2.25/0.99      | v1_zfmisc_1(X1_46)
% 2.25/0.99      | k6_domain_1(X1_46,X0_46) != X1_46 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_1378]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3626,plain,
% 2.25/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(sK2))
% 2.25/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2751]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3627,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 2.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3626]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3634,plain,
% 2.25/0.99      ( ~ v7_struct_0(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2762]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3635,plain,
% 2.25/0.99      ( v7_struct_0(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.25/0.99      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X0_46))) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3634]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3637,plain,
% 2.25/0.99      ( v7_struct_0(k1_tex_2(sK2,sK3)) != iProver_top
% 2.25/0.99      | l1_pre_topc(k1_tex_2(sK2,sK3)) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) = iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3635]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_7,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,X1)
% 2.25/0.99      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.25/0.99      | v1_xboole_0(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2775,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,X1_46)
% 2.25/0.99      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46))
% 2.25/0.99      | v1_xboole_0(X1_46) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3639,plain,
% 2.25/0.99      ( m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2775]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_8,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2774,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.25/0.99      | m1_subset_1(u1_struct_0(X0_47),k1_zfmisc_1(u1_struct_0(X1_47)))
% 2.25/0.99      | ~ l1_pre_topc(X1_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3642,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X0_47)
% 2.25/0.99      | m1_subset_1(u1_struct_0(k1_tex_2(X0_47,X0_46)),k1_zfmisc_1(u1_struct_0(X0_47)))
% 2.25/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2774]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3644,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3642]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_17,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.25/0.99      | v1_subset_1(X0,X1)
% 2.25/0.99      | X0 = X1 ),
% 2.25/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2771,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(X1_46))
% 2.25/0.99      | v1_subset_1(X0_46,X1_46)
% 2.25/0.99      | X0_46 = X1_46 ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3704,plain,
% 2.25/0.99      ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2771]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2776,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0_47,X1_47)
% 2.25/0.99      | ~ l1_pre_topc(X1_47)
% 2.25/0.99      | l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3746,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47)
% 2.25/0.99      | ~ l1_pre_topc(X1_47)
% 2.25/0.99      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2776]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3747,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(X0_47,X0_46),X1_47) != iProver_top
% 2.25/0.99      | l1_pre_topc(X1_47) != iProver_top
% 2.25/0.99      | l1_pre_topc(k1_tex_2(X0_47,X0_46)) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_3746]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3749,plain,
% 2.25/0.99      ( m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.25/0.99      | l1_pre_topc(k1_tex_2(sK2,sK3)) = iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3747]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3761,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2)
% 2.25/0.99      | v7_struct_0(sK2) != iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3759]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3720,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.25/0.99      | X0_46 = u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2771]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3877,plain,
% 2.25/0.99      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,X0_46)),u1_struct_0(sK2))
% 2.25/0.99      | u1_struct_0(k1_tex_2(sK2,X0_46)) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3720]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3880,plain,
% 2.25/0.99      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.25/0.99      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | u1_struct_0(k1_tex_2(sK2,sK3)) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3877]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2785,plain,
% 2.25/0.99      ( ~ v1_subset_1(X0_46,X1_46)
% 2.25/0.99      | v1_subset_1(X2_46,X3_46)
% 2.25/0.99      | X2_46 != X0_46
% 2.25/0.99      | X3_46 != X1_46 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3674,plain,
% 2.25/0.99      ( v1_subset_1(X0_46,X1_46)
% 2.25/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | X1_46 != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2785]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3836,plain,
% 2.25/0.99      ( v1_subset_1(X0_46,u1_struct_0(sK2))
% 2.25/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | X0_46 != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3674]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4109,plain,
% 2.25/0.99      ( v1_subset_1(sK1(sK2,k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3836]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3363,plain,
% 2.25/0.99      ( m1_subset_1(X0_46,X1_46) != iProver_top
% 2.25/0.99      | m1_subset_1(k6_domain_1(X1_46,X0_46),k1_zfmisc_1(X1_46)) = iProver_top
% 2.25/0.99      | v1_xboole_0(X1_46) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2775]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3367,plain,
% 2.25/0.99      ( X0_46 = X1_46
% 2.25/0.99      | m1_subset_1(X0_46,k1_zfmisc_1(X1_46)) != iProver_top
% 2.25/0.99      | v1_subset_1(X0_46,X1_46) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2771]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3941,plain,
% 2.25/0.99      ( k6_domain_1(X0_46,X1_46) = X0_46
% 2.25/0.99      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(X0_46,X1_46),X0_46) = iProver_top
% 2.25/0.99      | v1_xboole_0(X0_46) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_3363,c_3367]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_14,plain,
% 2.25/0.99      ( v1_tex_2(X0,X1)
% 2.25/0.99      | ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | ~ l1_pre_topc(X1)
% 2.25/0.99      | sK1(X1,X0) = u1_struct_0(X0) ),
% 2.25/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_775,plain,
% 2.25/0.99      ( ~ m1_pre_topc(X0,X1)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(X1)
% 2.25/0.99      | k1_tex_2(sK2,sK3) != X0
% 2.25/0.99      | sK1(X1,X0) = u1_struct_0(X0)
% 2.25/0.99      | sK2 != X1 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_228]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_776,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ l1_pre_topc(sK2)
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_775]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_778,plain,
% 2.25/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_776,c_27]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_779,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.25/0.99      inference(renaming,[status(thm)],[c_778]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2754,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_779]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3384,plain,
% 2.25/0.99      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | m1_pre_topc(k1_tex_2(sK2,sK3),sK2) != iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2754]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2937,plain,
% 2.25/0.99      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3)) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_2754,c_28,c_27,c_26,c_2834]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2939,plain,
% 2.25/0.99      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2937]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4712,plain,
% 2.25/0.99      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) != iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_3384,c_2939]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4718,plain,
% 2.25/0.99      ( sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_3941,c_4712]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4719,plain,
% 2.25/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2))
% 2.25/0.99      | sK1(sK2,k1_tex_2(sK2,sK3)) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4718]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2783,plain,
% 2.25/0.99      ( ~ v1_zfmisc_1(X0_46) | v1_zfmisc_1(X1_46) | X1_46 != X0_46 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4122,plain,
% 2.25/0.99      ( v1_zfmisc_1(X0_46)
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X0_47,X1_46)))
% 2.25/0.99      | X0_46 != u1_struct_0(k1_tex_2(X0_47,X1_46)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2783]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5050,plain,
% 2.25/0.99      ( v1_zfmisc_1(u1_struct_0(X0_47))
% 2.25/0.99      | ~ v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46)))
% 2.25/0.99      | u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46)) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_4122]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5052,plain,
% 2.25/0.99      ( u1_struct_0(X0_47) != u1_struct_0(k1_tex_2(X1_47,X0_46))
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(X0_47)) = iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(X1_47,X0_46))) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_5050]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5054,plain,
% 2.25/0.99      ( u1_struct_0(sK2) != u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(k1_tex_2(sK2,sK3))) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_5052]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2782,plain,
% 2.25/0.99      ( X0_46 != X1_46 | X2_46 != X1_46 | X2_46 = X0_46 ),
% 2.25/0.99      theory(equality) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3848,plain,
% 2.25/0.99      ( X0_46 != X1_46
% 2.25/0.99      | u1_struct_0(sK2) != X1_46
% 2.25/0.99      | u1_struct_0(sK2) = X0_46 ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2782]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4078,plain,
% 2.25/0.99      ( X0_46 != u1_struct_0(sK2)
% 2.25/0.99      | u1_struct_0(sK2) = X0_46
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3848]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4363,plain,
% 2.25/0.99      ( u1_struct_0(X0_47) != u1_struct_0(sK2)
% 2.25/0.99      | u1_struct_0(sK2) = u1_struct_0(X0_47)
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_4078]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5224,plain,
% 2.25/0.99      ( u1_struct_0(k1_tex_2(X0_47,X0_46)) != u1_struct_0(sK2)
% 2.25/0.99      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_4363]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5230,plain,
% 2.25/0.99      ( u1_struct_0(k1_tex_2(sK2,sK3)) != u1_struct_0(sK2)
% 2.25/0.99      | u1_struct_0(sK2) = u1_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_5224]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5295,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_5172,c_28,c_29,c_27,c_30,c_26,c_31,c_88,c_89,c_92,
% 2.25/0.99                 c_93,c_405,c_793,c_2803,c_2811,c_2834,c_2835,c_2841,
% 2.25/0.99                 c_3627,c_3637,c_3639,c_3644,c_3704,c_3749,c_3761,c_3880,
% 2.25/0.99                 c_4109,c_4719,c_5054,c_5230]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3387,plain,
% 2.25/0.99      ( k6_domain_1(X0_46,X1_46) != X0_46
% 2.25/0.99      | m1_subset_1(X1_46,X0_46) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(X0_46) = iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2751]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5301,plain,
% 2.25/0.99      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_5295,c_3387]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5398,plain,
% 2.25/0.99      ( v1_zfmisc_1(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(global_propositional_subsumption,
% 2.25/0.99                [status(thm)],
% 2.25/0.99                [c_5301,c_28,c_29,c_27,c_30,c_26,c_31,c_88,c_92,c_793,
% 2.25/0.99                 c_2803,c_2811,c_2834,c_2835,c_2841,c_3627,c_3637,c_3639,
% 2.25/0.99                 c_3644,c_3704,c_3749,c_3880,c_4109,c_4719,c_5054,c_5230]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_416,plain,
% 2.25/0.99      ( v2_struct_0(X0)
% 2.25/0.99      | ~ l1_pre_topc(X0)
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.25/0.99      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2760,plain,
% 2.25/0.99      ( v2_struct_0(X0_47)
% 2.25/0.99      | ~ l1_pre_topc(X0_47)
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(X0_47)) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_416]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5122,plain,
% 2.25/0.99      ( v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | ~ l1_pre_topc(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(X0_47,X0_46))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2760]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_5124,plain,
% 2.25/0.99      ( v2_struct_0(k1_tex_2(sK2,sK3))
% 2.25/0.99      | ~ l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.25/0.99      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK2,sK3))) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_5122]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_23,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.25/0.99      | ~ v7_struct_0(X1)
% 2.25/0.99      | v2_struct_0(X1)
% 2.25/0.99      | ~ l1_struct_0(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_430,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.25/0.99      | ~ v7_struct_0(X1)
% 2.25/0.99      | v2_struct_0(X1)
% 2.25/0.99      | ~ l1_pre_topc(X2)
% 2.25/0.99      | X1 != X2 ),
% 2.25/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_23]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_431,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X1),X0),u1_struct_0(X1))
% 2.25/0.99      | ~ v7_struct_0(X1)
% 2.25/0.99      | v2_struct_0(X1)
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2759,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47))
% 2.25/0.99      | ~ v7_struct_0(X0_47)
% 2.25/0.99      | v2_struct_0(X0_47)
% 2.25/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_431]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3379,plain,
% 2.25/0.99      ( m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.25/0.99      | v1_subset_1(k6_domain_1(u1_struct_0(X0_47),X0_46),u1_struct_0(X0_47)) != iProver_top
% 2.25/0.99      | v7_struct_0(X0_47) != iProver_top
% 2.25/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top ),
% 2.25/0.99      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4957,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(X0_47),X0_46) = u1_struct_0(X0_47)
% 2.25/0.99      | m1_subset_1(X0_46,u1_struct_0(X0_47)) != iProver_top
% 2.25/0.99      | v7_struct_0(X0_47) != iProver_top
% 2.25/0.99      | v2_struct_0(X0_47) = iProver_top
% 2.25/0.99      | l1_pre_topc(X0_47) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(X0_47)) = iProver_top ),
% 2.25/0.99      inference(superposition,[status(thm)],[c_3941,c_3379]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_4959,plain,
% 2.25/0.99      ( k6_domain_1(u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 2.25/0.99      | m1_subset_1(sK3,u1_struct_0(sK2)) != iProver_top
% 2.25/0.99      | v7_struct_0(sK2) != iProver_top
% 2.25/0.99      | v2_struct_0(sK2) = iProver_top
% 2.25/0.99      | l1_pre_topc(sK2) != iProver_top
% 2.25/0.99      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_4957]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_3748,plain,
% 2.25/0.99      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/0.99      | l1_pre_topc(k1_tex_2(sK2,sK3))
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_3746]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2850,plain,
% 2.25/0.99      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/0.99      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/0.99      | ~ v7_struct_0(sK2)
% 2.25/0.99      | v2_struct_0(sK2)
% 2.25/0.99      | ~ l1_pre_topc(sK2) ),
% 2.25/0.99      inference(instantiation,[status(thm)],[c_2759]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_22,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.25/0.99      | v2_struct_0(X1)
% 2.25/0.99      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 2.25/0.99      | ~ l1_pre_topc(X1) ),
% 2.25/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.25/0.99  
% 2.25/0.99  cnf(c_2768,plain,
% 2.25/0.99      ( ~ m1_subset_1(X0_46,u1_struct_0(X0_47))
% 2.25/0.99      | v2_struct_0(X0_47)
% 2.25/0.99      | ~ v2_struct_0(k1_tex_2(X0_47,X0_46))
% 2.25/0.99      | ~ l1_pre_topc(X0_47) ),
% 2.25/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_2837,plain,
% 2.25/1.00      ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
% 2.25/1.00      | ~ v2_struct_0(k1_tex_2(sK2,sK3))
% 2.25/1.00      | v2_struct_0(sK2)
% 2.25/1.00      | ~ l1_pre_topc(sK2) ),
% 2.25/1.00      inference(instantiation,[status(thm)],[c_2768]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_16,plain,
% 2.25/1.00      ( ~ v1_tex_2(X0,X1)
% 2.25/1.00      | ~ m1_pre_topc(X0,X1)
% 2.25/1.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.25/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.25/1.00      | ~ l1_pre_topc(X1) ),
% 2.25/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_169,plain,
% 2.25/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.25/1.00      | ~ v1_tex_2(X0,X1)
% 2.25/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.25/1.00      | ~ l1_pre_topc(X1) ),
% 2.25/1.00      inference(global_propositional_subsumption,
% 2.25/1.00                [status(thm)],
% 2.25/1.00                [c_16,c_8]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_170,plain,
% 2.25/1.00      ( ~ v1_tex_2(X0,X1)
% 2.25/1.00      | ~ m1_pre_topc(X0,X1)
% 2.25/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.25/1.00      | ~ l1_pre_topc(X1) ),
% 2.25/1.00      inference(renaming,[status(thm)],[c_169]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_25,negated_conjecture,
% 2.25/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.25/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_230,plain,
% 2.25/1.00      ( v1_tex_2(k1_tex_2(sK2,sK3),sK2)
% 2.25/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2)) ),
% 2.25/1.00      inference(prop_impl,[status(thm)],[c_25]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_809,plain,
% 2.25/1.00      ( ~ m1_pre_topc(X0,X1)
% 2.25/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/1.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 2.25/1.00      | ~ l1_pre_topc(X1)
% 2.25/1.00      | k1_tex_2(sK2,sK3) != X0
% 2.25/1.00      | sK2 != X1 ),
% 2.25/1.00      inference(resolution_lifted,[status(thm)],[c_170,c_230]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_810,plain,
% 2.25/1.00      ( ~ m1_pre_topc(k1_tex_2(sK2,sK3),sK2)
% 2.25/1.00      | v1_subset_1(k6_domain_1(u1_struct_0(sK2),sK3),u1_struct_0(sK2))
% 2.25/1.00      | v1_subset_1(u1_struct_0(k1_tex_2(sK2,sK3)),u1_struct_0(sK2))
% 2.25/1.00      | ~ l1_pre_topc(sK2) ),
% 2.25/1.00      inference(unflattening,[status(thm)],[c_809]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(c_404,plain,
% 2.25/1.00      ( v7_struct_0(sK2)
% 2.25/1.00      | ~ l1_pre_topc(sK2)
% 2.25/1.00      | ~ v1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.25/1.00      inference(instantiation,[status(thm)],[c_402]) ).
% 2.25/1.00  
% 2.25/1.00  cnf(contradiction,plain,
% 2.25/1.00      ( $false ),
% 2.25/1.00      inference(minisat,
% 2.25/1.00                [status(thm)],
% 2.25/1.00                [c_6007,c_5398,c_5124,c_4959,c_3748,c_3644,c_3626,c_2850,
% 2.25/1.00                 c_2837,c_2834,c_810,c_405,c_404,c_93,c_89,c_31,c_26,
% 2.25/1.00                 c_30,c_27,c_29,c_28]) ).
% 2.25/1.00  
% 2.25/1.00  
% 2.25/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.25/1.00  
% 2.25/1.00  ------                               Statistics
% 2.25/1.00  
% 2.25/1.00  ------ General
% 2.25/1.00  
% 2.25/1.00  abstr_ref_over_cycles:                  0
% 2.25/1.00  abstr_ref_under_cycles:                 0
% 2.25/1.00  gc_basic_clause_elim:                   0
% 2.25/1.00  forced_gc_time:                         0
% 2.25/1.00  parsing_time:                           0.013
% 2.25/1.00  unif_index_cands_time:                  0.
% 2.25/1.00  unif_index_add_time:                    0.
% 2.25/1.00  orderings_time:                         0.
% 2.25/1.00  out_proof_time:                         0.014
% 2.25/1.00  total_time:                             0.187
% 2.25/1.00  num_of_symbols:                         51
% 2.25/1.00  num_of_terms:                           3060
% 2.25/1.00  
% 2.25/1.00  ------ Preprocessing
% 2.25/1.00  
% 2.25/1.00  num_of_splits:                          0
% 2.25/1.00  num_of_split_atoms:                     0
% 2.25/1.00  num_of_reused_defs:                     0
% 2.25/1.00  num_eq_ax_congr_red:                    7
% 2.25/1.00  num_of_sem_filtered_clauses:            1
% 2.25/1.00  num_of_subtypes:                        2
% 2.25/1.00  monotx_restored_types:                  1
% 2.25/1.00  sat_num_of_epr_types:                   0
% 2.25/1.00  sat_num_of_non_cyclic_types:            0
% 2.25/1.00  sat_guarded_non_collapsed_types:        0
% 2.25/1.00  num_pure_diseq_elim:                    0
% 2.25/1.00  simp_replaced_by:                       0
% 2.25/1.00  res_preprocessed:                       145
% 2.25/1.00  prep_upred:                             0
% 2.25/1.00  prep_unflattend:                        105
% 2.25/1.00  smt_new_axioms:                         0
% 2.25/1.00  pred_elim_cands:                        8
% 2.25/1.00  pred_elim:                              2
% 2.25/1.00  pred_elim_cl:                           0
% 2.25/1.00  pred_elim_cycles:                       13
% 2.25/1.00  merged_defs:                            2
% 2.25/1.00  merged_defs_ncl:                        0
% 2.25/1.00  bin_hyper_res:                          2
% 2.25/1.00  prep_cycles:                            4
% 2.25/1.00  pred_elim_time:                         0.043
% 2.25/1.00  splitting_time:                         0.
% 2.25/1.00  sem_filter_time:                        0.
% 2.25/1.00  monotx_time:                            0.001
% 2.25/1.00  subtype_inf_time:                       0.002
% 2.25/1.00  
% 2.25/1.00  ------ Problem properties
% 2.25/1.00  
% 2.25/1.00  clauses:                                28
% 2.25/1.00  conjectures:                            3
% 2.25/1.00  epr:                                    4
% 2.25/1.00  horn:                                   19
% 2.25/1.00  ground:                                 7
% 2.25/1.00  unary:                                  3
% 2.25/1.00  binary:                                 2
% 2.25/1.00  lits:                                   85
% 2.25/1.00  lits_eq:                                5
% 2.25/1.00  fd_pure:                                0
% 2.25/1.00  fd_pseudo:                              0
% 2.25/1.00  fd_cond:                                0
% 2.25/1.00  fd_pseudo_cond:                         1
% 2.25/1.00  ac_symbols:                             0
% 2.25/1.00  
% 2.25/1.00  ------ Propositional Solver
% 2.25/1.00  
% 2.25/1.00  prop_solver_calls:                      28
% 2.25/1.00  prop_fast_solver_calls:                 1561
% 2.25/1.00  smt_solver_calls:                       0
% 2.25/1.00  smt_fast_solver_calls:                  0
% 2.25/1.00  prop_num_of_clauses:                    1349
% 2.25/1.00  prop_preprocess_simplified:             6394
% 2.25/1.00  prop_fo_subsumed:                       57
% 2.25/1.00  prop_solver_time:                       0.
% 2.25/1.00  smt_solver_time:                        0.
% 2.25/1.00  smt_fast_solver_time:                   0.
% 2.25/1.00  prop_fast_solver_time:                  0.
% 2.25/1.00  prop_unsat_core_time:                   0.
% 2.25/1.00  
% 2.25/1.00  ------ QBF
% 2.25/1.00  
% 2.25/1.00  qbf_q_res:                              0
% 2.25/1.00  qbf_num_tautologies:                    0
% 2.25/1.00  qbf_prep_cycles:                        0
% 2.25/1.00  
% 2.25/1.00  ------ BMC1
% 2.25/1.00  
% 2.25/1.00  bmc1_current_bound:                     -1
% 2.25/1.00  bmc1_last_solved_bound:                 -1
% 2.25/1.00  bmc1_unsat_core_size:                   -1
% 2.25/1.00  bmc1_unsat_core_parents_size:           -1
% 2.25/1.00  bmc1_merge_next_fun:                    0
% 2.25/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.25/1.00  
% 2.25/1.00  ------ Instantiation
% 2.25/1.00  
% 2.25/1.00  inst_num_of_clauses:                    388
% 2.25/1.00  inst_num_in_passive:                    161
% 2.25/1.00  inst_num_in_active:                     219
% 2.25/1.00  inst_num_in_unprocessed:                7
% 2.25/1.00  inst_num_of_loops:                      269
% 2.25/1.00  inst_num_of_learning_restarts:          0
% 2.25/1.00  inst_num_moves_active_passive:          45
% 2.25/1.00  inst_lit_activity:                      0
% 2.25/1.00  inst_lit_activity_moves:                0
% 2.25/1.00  inst_num_tautologies:                   0
% 2.25/1.00  inst_num_prop_implied:                  0
% 2.25/1.00  inst_num_existing_simplified:           0
% 2.25/1.00  inst_num_eq_res_simplified:             0
% 2.25/1.00  inst_num_child_elim:                    0
% 2.25/1.00  inst_num_of_dismatching_blockings:      128
% 2.25/1.00  inst_num_of_non_proper_insts:           432
% 2.25/1.00  inst_num_of_duplicates:                 0
% 2.25/1.00  inst_inst_num_from_inst_to_res:         0
% 2.25/1.00  inst_dismatching_checking_time:         0.
% 2.25/1.00  
% 2.25/1.00  ------ Resolution
% 2.25/1.00  
% 2.25/1.00  res_num_of_clauses:                     0
% 2.25/1.00  res_num_in_passive:                     0
% 2.25/1.00  res_num_in_active:                      0
% 2.25/1.00  res_num_of_loops:                       149
% 2.25/1.00  res_forward_subset_subsumed:            42
% 2.25/1.00  res_backward_subset_subsumed:           0
% 2.25/1.00  res_forward_subsumed:                   1
% 2.25/1.00  res_backward_subsumed:                  2
% 2.25/1.00  res_forward_subsumption_resolution:     2
% 2.25/1.00  res_backward_subsumption_resolution:    0
% 2.25/1.00  res_clause_to_clause_subsumption:       219
% 2.25/1.00  res_orphan_elimination:                 0
% 2.25/1.00  res_tautology_del:                      103
% 2.25/1.00  res_num_eq_res_simplified:              0
% 2.25/1.00  res_num_sel_changes:                    0
% 2.25/1.00  res_moves_from_active_to_pass:          0
% 2.25/1.00  
% 2.25/1.00  ------ Superposition
% 2.25/1.00  
% 2.25/1.00  sup_time_total:                         0.
% 2.25/1.00  sup_time_generating:                    0.
% 2.25/1.00  sup_time_sim_full:                      0.
% 2.25/1.00  sup_time_sim_immed:                     0.
% 2.25/1.00  
% 2.25/1.00  sup_num_of_clauses:                     60
% 2.25/1.00  sup_num_in_active:                      48
% 2.25/1.00  sup_num_in_passive:                     12
% 2.25/1.00  sup_num_of_loops:                       52
% 2.25/1.00  sup_fw_superposition:                   21
% 2.25/1.00  sup_bw_superposition:                   35
% 2.25/1.00  sup_immediate_simplified:               17
% 2.25/1.00  sup_given_eliminated:                   0
% 2.25/1.00  comparisons_done:                       0
% 2.25/1.00  comparisons_avoided:                    0
% 2.25/1.00  
% 2.25/1.00  ------ Simplifications
% 2.25/1.00  
% 2.25/1.00  
% 2.25/1.00  sim_fw_subset_subsumed:                 16
% 2.25/1.00  sim_bw_subset_subsumed:                 1
% 2.25/1.00  sim_fw_subsumed:                        1
% 2.25/1.00  sim_bw_subsumed:                        0
% 2.25/1.00  sim_fw_subsumption_res:                 0
% 2.25/1.00  sim_bw_subsumption_res:                 0
% 2.25/1.00  sim_tautology_del:                      2
% 2.25/1.00  sim_eq_tautology_del:                   3
% 2.25/1.00  sim_eq_res_simp:                        0
% 2.25/1.00  sim_fw_demodulated:                     0
% 2.25/1.00  sim_bw_demodulated:                     4
% 2.25/1.00  sim_light_normalised:                   0
% 2.25/1.00  sim_joinable_taut:                      0
% 2.25/1.00  sim_joinable_simp:                      0
% 2.25/1.00  sim_ac_normalised:                      0
% 2.25/1.00  sim_smt_subsumption:                    0
% 2.25/1.00  
%------------------------------------------------------------------------------
