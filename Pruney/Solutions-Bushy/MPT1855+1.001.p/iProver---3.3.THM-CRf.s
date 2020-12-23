%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1855+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:40 EST 2020

% Result     : Theorem 6.43s
% Output     : CNFRefutation 6.43s
% Verified   : 
% Statistics : Number of formulae       :  208 (1909 expanded)
%              Number of clauses        :  133 ( 679 expanded)
%              Number of leaves         :   21 ( 418 expanded)
%              Depth                    :   26
%              Number of atoms          :  704 (9047 expanded)
%              Number of equality atoms :  243 (1766 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f40,f49,f48])).

fof(f77,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f76,plain,(
    v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f21])).

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
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

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

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f78,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1380,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_2094,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1380])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1388,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49)))
    | ~ l1_pre_topc(X1_49) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_2086,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_subset_1(u1_struct_0(X0_49),k1_zfmisc_1(u1_struct_0(X1_49))) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1389,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | l1_pre_topc(X0_49) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2085,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_2450,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_2085])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2361,plain,
    ( ~ m1_pre_topc(sK2,X0_49)
    | ~ l1_pre_topc(X0_49)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_2362,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2361])).

cnf(c_2364,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2362])).

cnf(c_2530,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_29,c_32,c_2364])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_565,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_2])).

cnf(c_1371,plain,
    ( m1_subset_1(sK0(X0_49),u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ v7_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_565])).

cnf(c_2103,plain,
    ( m1_subset_1(sK0(X0_49),u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1387,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48)
    | k6_domain_1(X1_48,X0_48) = k1_tarski(X0_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2087,plain,
    ( k6_domain_1(X0_48,X1_48) = k1_tarski(X1_48)
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1387])).

cnf(c_3107,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = k1_tarski(sK0(X0_49))
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2103,c_2087])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_551,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_1372,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_551])).

cnf(c_1480,plain,
    ( v1_xboole_0(u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1372])).

cnf(c_4988,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = k1_tarski(sK0(X0_49))
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3107,c_1480])).

cnf(c_4999,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = k1_tarski(sK0(sK2))
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_4988])).

cnf(c_1,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_582,plain,
    ( ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_1])).

cnf(c_1370,plain,
    ( ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | ~ v7_struct_0(X0_49)
    | k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = u1_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_582])).

cnf(c_2104,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(X0_49)) = u1_struct_0(X0_49)
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top
    | v7_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1370])).

cnf(c_3245,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2530,c_2104])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_24,negated_conjecture,
    ( v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2332,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1370])).

cnf(c_2363,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_3326,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3245,c_26,c_25,c_24,c_23,c_2332,c_2363])).

cnf(c_5027,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2)
    | v2_struct_0(sK2) = iProver_top
    | v7_struct_0(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4999,c_3326])).

cnf(c_30,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_31,plain,
    ( v7_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5193,plain,
    ( k1_tarski(sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5027,c_30,c_31])).

cnf(c_16,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_232,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_233,plain,
    ( ~ r1_tarski(k1_tarski(X0),X1)
    | r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_232])).

cnf(c_18,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_236,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_410,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X3 != X1
    | k1_tarski(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_233,c_236])).

cnf(c_411,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_960,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_411])).

cnf(c_1373,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X1_48)) ),
    inference(subtyping,[status(esa)],[c_960])).

cnf(c_2101,plain,
    ( r2_hidden(X0_48,X1_48) = iProver_top
    | m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X1_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1373])).

cnf(c_5198,plain,
    ( r2_hidden(sK0(sK2),X0_48) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5193,c_2101])).

cnf(c_5280,plain,
    ( r2_hidden(sK0(sK2),u1_struct_0(X0_49)) = iProver_top
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_5198])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1384,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | m1_subset_1(X0_48,X2_48)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(X2_48)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_2090,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_48,X2_48) = iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(X2_48)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_2665,plain,
    ( r2_hidden(X0_48,u1_struct_0(X0_49)) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_subset_1(X0_48,u1_struct_0(X1_49)) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_2086,c_2090])).

cnf(c_5771,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X1_49)) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_2665])).

cnf(c_1445,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | l1_pre_topc(X1_49) != iProver_top
    | l1_pre_topc(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1389])).

cnf(c_20439,plain,
    ( l1_pre_topc(X1_49) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X1_49)) = iProver_top
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | m1_pre_topc(X0_49,X1_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5771,c_1445])).

cnf(c_20440,plain,
    ( m1_pre_topc(X0_49,X1_49) != iProver_top
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X1_49)) = iProver_top
    | l1_pre_topc(X1_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_20439])).

cnf(c_20447,plain,
    ( m1_pre_topc(sK2,sK2) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_20440])).

cnf(c_770,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_565,c_24])).

cnf(c_771,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_770])).

cnf(c_772,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_771])).

cnf(c_2329,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_2330,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2329])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1385,plain,
    ( r2_hidden(X0_48,X1_48)
    | ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2432,plain,
    ( r2_hidden(sK0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2433,plain,
    ( r2_hidden(sK0(sK2),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2432])).

cnf(c_2505,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1372])).

cnf(c_2506,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2505])).

cnf(c_2578,plain,
    ( ~ r2_hidden(sK0(sK2),u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2),X0_48)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(X0_48)) ),
    inference(instantiation,[status(thm)],[c_1384])).

cnf(c_2837,plain,
    ( ~ r2_hidden(sK0(sK2),u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2578])).

cnf(c_2839,plain,
    ( r2_hidden(sK0(sK2),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2837])).

cnf(c_20476,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20447,c_29,c_30,c_32,c_772,c_2330,c_2364,c_2433,c_2506,c_2839])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_5,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_180,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_5])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_180])).

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

cnf(c_186,plain,
    ( v2_struct_0(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_181,c_7,c_6])).

cnf(c_187,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_186])).

cnf(c_1375,plain,
    ( ~ m1_subset_1(X0_48,u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49)
    | k6_domain_1(u1_struct_0(X0_49),X0_48) = u1_struct_0(k1_tex_2(X0_49,X0_48)) ),
    inference(subtyping,[status(esa)],[c_187])).

cnf(c_2099,plain,
    ( k6_domain_1(u1_struct_0(X0_49),X0_48) = u1_struct_0(k1_tex_2(X0_49,X0_48))
    | m1_subset_1(X0_48,u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top
    | v2_struct_0(X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1375])).

cnf(c_20484,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2)))
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_20476,c_2099])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1386,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | m1_subset_1(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2088,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_48,X1_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_5769,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | m1_subset_1(sK0(sK2),u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_2088])).

cnf(c_6009,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = k1_tarski(sK0(sK2))
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_5769,c_2087])).

cnf(c_6014,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) = iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6009,c_5193])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1382,plain,
    ( ~ r2_hidden(X0_48,X1_48)
    | ~ v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2092,plain,
    ( r2_hidden(X0_48,X1_48) != iProver_top
    | v1_xboole_0(X1_48) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_5768,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | v1_xboole_0(u1_struct_0(X0_49)) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(superposition,[status(thm)],[c_5280,c_2092])).

cnf(c_6361,plain,
    ( m1_pre_topc(sK2,X0_49) != iProver_top
    | k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6014,c_5768])).

cnf(c_6362,plain,
    ( k6_domain_1(u1_struct_0(X0_49),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,X0_49) != iProver_top
    | l1_pre_topc(X0_49) != iProver_top ),
    inference(renaming,[status(thm)],[c_6361])).

cnf(c_6370,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2094,c_6362])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_69,plain,
    ( v1_xboole_0(u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_71,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(c_73,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_75,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_6075,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | v1_xboole_0(u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6014])).

cnf(c_6499,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6370,c_28,c_29,c_32,c_71,c_75,c_6075])).

cnf(c_20511,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2)
    | l1_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20484,c_6499])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1383,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(X2_49,X1_49)
    | ~ l1_pre_topc(X1_49)
    | g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49)) = g1_pre_topc(u1_struct_0(X2_49),u1_pre_topc(X2_49))
    | u1_struct_0(X0_49) != u1_struct_0(X2_49) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_3507,plain,
    ( ~ m1_pre_topc(X0_49,X1_49)
    | ~ m1_pre_topc(k1_tex_2(X1_49,sK0(sK2)),X1_49)
    | ~ l1_pre_topc(X1_49)
    | g1_pre_topc(u1_struct_0(k1_tex_2(X1_49,sK0(sK2))),u1_pre_topc(k1_tex_2(X1_49,sK0(sK2)))) = g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))
    | u1_struct_0(k1_tex_2(X1_49,sK0(sK2))) != u1_struct_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_4441,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_1401,plain,
    ( X0_50 != X1_50
    | X2_50 != X1_50
    | X2_50 = X0_50 ),
    theory(equality)).

cnf(c_3173,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != X0_50
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_50
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_3212,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2))))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_3173])).

cnf(c_22,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0)),u1_pre_topc(k1_tex_2(sK1,X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1381,negated_conjecture,
    ( ~ m1_subset_1(X0_48,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_48)),u1_pre_topc(k1_tex_2(sK1,X0_48))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_2838,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1392,plain,
    ( m1_pre_topc(k1_tex_2(X0_49,X0_48),X0_49)
    | ~ m1_subset_1(X0_48,u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_2788,plain,
    ( m1_pre_topc(k1_tex_2(X0_49,sK0(sK2)),X0_49)
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(X0_49))
    | ~ l1_pre_topc(X0_49)
    | v2_struct_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1392])).

cnf(c_2804,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2788])).

cnf(c_1395,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_2463,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1395])).

cnf(c_2351,plain,
    ( ~ m1_pre_topc(X0_49,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0_49),u1_pre_topc(X0_49))
    | u1_struct_0(sK2) != u1_struct_0(X0_49) ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_2397,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20511,c_4441,c_3212,c_2838,c_2837,c_2804,c_2505,c_2463,c_2432,c_2397,c_2363,c_2329,c_771,c_23,c_25,c_29,c_26,c_28,c_27])).


%------------------------------------------------------------------------------
