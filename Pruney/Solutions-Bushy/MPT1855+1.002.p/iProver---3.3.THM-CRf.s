%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1855+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  193 (12591 expanded)
%              Number of clauses        :  119 (4335 expanded)
%              Number of leaves         :   18 (2769 expanded)
%              Depth                    :   35
%              Number of atoms          :  665 (59857 expanded)
%              Number of equality atoms :  244 (12179 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ! [X2] :
            ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_pre_topc(sK2,X0)
        & v7_struct_0(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(X0,X2)),u1_pre_topc(k1_tex_2(X0,X2)))
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_pre_topc(X1,X0)
            & v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
              | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_pre_topc(X1,sK1)
          & v7_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_pre_topc(sK2,sK1)
    & v7_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f42,f49,f48])).

fof(f74,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f43])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v7_struct_0(X0)
          | ! [X1] :
              ( u1_struct_0(X0) != k6_domain_1(u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
            & m1_subset_1(sK0(X0),u1_struct_0(X0)) )
          | ~ v7_struct_0(X0) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f44,f45])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f73,plain,(
    v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
     => r2_hidden(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f70,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f76,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1015,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1502,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1015])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1019,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ l1_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1498,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49))) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1019])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1020,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1497,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_1741,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1497])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1744,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1741,c_26])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_425,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_1])).

cnf(c_1005,plain,
    ( ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ v7_struct_0(X0_49)
    | k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = u1_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_1512,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = u1_struct_0(X0_49)
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1005])).

cnf(c_2387,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_1512])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_27,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,plain,
    ( v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1724,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_1725,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_2468,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2387,c_26,c_27,c_28,c_1725,c_1741])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1021,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48))
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1496,plain,
    ( m1_subset_1(X0_48,X1_48) != iProver_top
    | m1_subset_1(k6_domain_1(X1_48,X0_48),k1_zfmisc_1(X1_48)) = iProver_top
    | v1_xboole_0(X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1021])).

cnf(c_2472,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2468,c_1496])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_408,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_625,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_408,c_21])).

cnf(c_626,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_627,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_394,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_1007,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1910,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_1911,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1910])).

cnf(c_2561,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2472,c_26,c_27,c_627,c_1741,c_1911])).

cnf(c_1006,plain,
    ( m1_subset_1(sK0(X0_49),u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ v7_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_408])).

cnf(c_1511,plain,
    ( m1_subset_1(sK0(X0_49),u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1018,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48)
    | k6_domain_1(X1_48,X0_48) = k1_tarski(X0_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1499,plain,
    ( k6_domain_1(X0_48,X1_48) = k1_tarski(X1_48)
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2167,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = k1_tarski(sK0(X0_49))
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1499])).

cnf(c_1105,plain,
    ( v1_xboole_0(u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1007])).

cnf(c_3630,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = k1_tarski(sK0(X0_49))
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2167,c_1105])).

cnf(c_3641,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = k1_tarski(sK0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_3630])).

cnf(c_3669,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3641,c_2468])).

cnf(c_4004,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_27,c_28])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_296,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X3 != X1
    | k1_tarski(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_15])).

cnf(c_297,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_296])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_325,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X2)) ),
    inference(resolution,[status(thm)],[c_297,c_16])).

cnf(c_1008,plain,
    ( m1_subset_1(X0_48,X1_48)
    | ~ m1_subset_1(X2_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_325])).

cnf(c_1509,plain,
    ( m1_subset_1(X0_48,X1_48) = iProver_top
    | m1_subset_1(X2_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X2_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_4007,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(sK0(sK2),X1_48) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1509])).

cnf(c_4219,plain,
    ( m1_subset_1(sK0(sK2),X0_48) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_4007])).

cnf(c_4241,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_4219])).

cnf(c_4830,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = k1_tarski(sK0(sK2))
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_4241,c_1499])).

cnf(c_4840,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4830,c_4004])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_tarski(X2),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_297,c_17])).

cnf(c_1009,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X1_48))
    | ~ m1_subset_1(k1_tarski(X2_48),k1_zfmisc_1(X0_48))
    | ~ v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_311])).

cnf(c_1508,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(k1_tarski(X2_48),k1_zfmisc_1(X0_48)) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_4008,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(X1_48)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_4004,c_1508])).

cnf(c_4119,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) != iProver_top
    | v1_xboole_0(X0_48) != iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_4008])).

cnf(c_4141,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_4119])).

cnf(c_5354,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4840,c_4141])).

cnf(c_5355,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_5354])).

cnf(c_5363,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_5355])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_54,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_56,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_54])).

cnf(c_58,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_60,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_58])).

cnf(c_4931,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4840])).

cnf(c_5366,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5363,c_25,c_26,c_29,c_56,c_60,c_4931])).

cnf(c_5371,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5366,c_1496])).

cnf(c_1721,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1722,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1721])).

cnf(c_5463,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5371,c_26,c_29,c_1722])).

cnf(c_5471,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5463,c_4219])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_5,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_159,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_160,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_159])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_165,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_160,c_7,c_6])).

cnf(c_166,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_1010,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | k6_domain_1(u1_struct_0(X0_49),X0_48) = u1_struct_0(k1_tex_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_166])).

cnf(c_1507,plain,
    ( k6_domain_1(u1_struct_0(X0_49),X0_48) = u1_struct_0(k1_tex_2(X0_49,X0_48))
    | m1_subset_1(X0_48,u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1010])).

cnf(c_5976,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2)))
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5471,c_1507])).

cnf(c_6016,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2)
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5976,c_5366])).

cnf(c_6034,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6016,c_25,c_26])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1017,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X2_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49)) = g1_pre_topc(u1_struct_0(X2_49),u1_pre_topc(X2_49))
    | u1_struct_0(X0_49) != u1_struct_0(X2_49) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1500,plain,
    ( g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49)) = g1_pre_topc(u1_struct_0(X1_49),u1_pre_topc(X1_49))
    | u1_struct_0(X0_49) != u1_struct_0(X1_49)
    | m1_pre_topc(X0_49,X2_49) != iProver_top
    | m1_pre_topc(X1_49,X2_49) != iProver_top
    | l1_pre_topc(X2_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1017])).

cnf(c_6052,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))
    | u1_struct_0(X0_49) != u1_struct_0(sK2)
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_6034,c_1500])).

cnf(c_6107,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))
    | u1_struct_0(X0_49) != u1_struct_0(sK2)
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6052,c_6034])).

cnf(c_7397,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),X0_49) != iProver_top
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_6107])).

cnf(c_7421,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1) != iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7397])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0)),u1_pre_topc(k1_tex_2(sK1,X0))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1016,negated_conjecture,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_48)),u1_pre_topc(k1_tex_2(sK1,X0_48))) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1501,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_48)),u1_pre_topc(k1_tex_2(sK1,X0_48)))
    | m1_subset_1(X0_48,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1016])).

cnf(c_6058,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6034,c_1501])).

cnf(c_4252,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4241])).

cnf(c_1024,plain,
    ( m1_pre_topc(k1_tex_2(X0_49,X0_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2215,plain,
    ( m1_pre_topc(k1_tex_2(X0_49,sK0(sK2)),X0_49)
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_2230,plain,
    ( m1_pre_topc(k1_tex_2(X0_49,sK0(sK2)),X0_49) = iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2215])).

cnf(c_2232,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1) = iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2230])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7421,c_6058,c_4252,c_2232,c_29,c_26,c_25])).


%------------------------------------------------------------------------------
