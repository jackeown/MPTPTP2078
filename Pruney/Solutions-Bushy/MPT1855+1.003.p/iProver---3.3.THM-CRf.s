%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1855+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:41 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 247 expanded)
%              Number of clauses        :   91 ( 107 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1112 expanded)
%              Number of equality atoms :  150 ( 243 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f45,plain,
    ( ! [X2] :
        ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    & m1_pre_topc(sK2,sK1)
    & v7_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f44,f43])).

fof(f68,plain,(
    ! [X2] :
      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X2)),u1_pre_topc(k1_tex_2(sK1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

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
    inference(flattening,[],[f19])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X2) = k6_domain_1(u1_struct_0(X0),X1)
      | k1_tex_2(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f69,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_tex_2(X0,X1)) = k6_domain_1(u1_struct_0(X0),X1)
      | ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ v1_pre_topc(k1_tex_2(X0,X1))
      | v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f4,axiom,(
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
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
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
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0] :
      ( ( v7_struct_0(X0)
      <=> ? [X1] :
            ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
        & m1_subset_1(sK0(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f48,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k6_domain_1(u1_struct_0(X0),sK0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_993,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_2520,plain,
    ( X0_47 != X1_47
    | u1_struct_0(X0_48) != X1_47
    | u1_struct_0(X0_48) = X0_47 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_5396,plain,
    ( X0_47 != k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) = X0_47
    | u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) != k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_12832,plain,
    ( u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) != k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5396])).

cnf(c_12841,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != k6_domain_1(u1_struct_0(sK1),sK0(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK1),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_12832])).

cnf(c_5123,plain,
    ( X0_47 != X1_47
    | X0_47 = k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_8726,plain,
    ( X0_47 != k6_domain_1(X1_47,X2_47)
    | X0_47 = k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) != k6_domain_1(X1_47,X2_47) ),
    inference(instantiation,[status(thm)],[c_5123])).

cnf(c_10834,plain,
    ( k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) != k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | u1_struct_0(sK2) = k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_8726])).

cnf(c_10835,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) != k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK1),sK0(sK2))
    | u1_struct_0(sK2) != k6_domain_1(u1_struct_0(sK2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_10834])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | u1_struct_0(X0) != u1_struct_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_980,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ m1_pre_topc(X2_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48)) = g1_pre_topc(u1_struct_0(X2_48),u1_pre_topc(X2_48))
    | u1_struct_0(X0_48) != u1_struct_0(X2_48) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_7883,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),X0_48)
    | ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_7885,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_7883])).

cnf(c_3560,plain,
    ( X0_47 != X1_47
    | X0_47 = k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) != X1_47 ),
    inference(instantiation,[status(thm)],[c_993])).

cnf(c_5016,plain,
    ( X0_47 = k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | X0_47 != k1_tarski(sK0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) != k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_6715,plain,
    ( k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) = k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) != k1_tarski(sK0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) != k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5016])).

cnf(c_6716,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | k6_domain_1(u1_struct_0(sK1),sK0(sK2)) != k1_tarski(sK0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) != k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6715])).

cnf(c_991,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_4809,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_3264,plain,
    ( X0_47 != u1_struct_0(X0_48)
    | u1_struct_0(X0_48) = X0_47
    | u1_struct_0(X0_48) != u1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_3815,plain,
    ( k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) != u1_struct_0(k1_tex_2(X0_48,sK0(sK2)))
    | u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) = k6_domain_1(u1_struct_0(X0_48),sK0(sK2))
    | u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) != u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_3816,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK0(sK2)) != u1_struct_0(k1_tex_2(sK1,sK0(sK2)))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = k6_domain_1(u1_struct_0(sK1),sK0(sK2))
    | u1_struct_0(k1_tex_2(sK1,sK0(sK2))) != u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3815])).

cnf(c_3811,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(sK2)) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k6_domain_1(u1_struct_0(sK2),sK0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3264])).

cnf(c_990,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_3776,plain,
    ( u1_struct_0(k1_tex_2(sK1,sK0(sK2))) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_994,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_2295,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != X0_48
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != X0_48
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_994])).

cnf(c_2801,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0_48),u1_pre_topc(X0_48))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_2295])).

cnf(c_3641,plain,
    ( g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2))))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_2801])).

cnf(c_995,plain,
    ( X0_48 != X1_48
    | u1_struct_0(X0_48) = u1_struct_0(X1_48) ),
    theory(equality)).

cnf(c_2430,plain,
    ( sK2 != X0_48
    | u1_struct_0(sK2) = u1_struct_0(X0_48) ),
    inference(instantiation,[status(thm)],[c_995])).

cnf(c_3103,plain,
    ( sK2 != sK2
    | u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2430])).

cnf(c_2368,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_991])).

cnf(c_17,negated_conjecture,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0)),u1_pre_topc(k1_tex_2(sK1,X0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_979,negated_conjecture,
    ( ~ m1_subset_1(X0_47,u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,X0_47)),u1_pre_topc(k1_tex_2(sK1,X0_47))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_2056,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(k1_tex_2(sK1,sK0(sK2))),u1_pre_topc(k1_tex_2(sK1,sK0(sK2)))) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_981,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | v1_xboole_0(X1_47)
    | k6_domain_1(X1_47,X0_47) = k1_tarski(X0_47) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2031,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(X0_48))
    | v1_xboole_0(u1_struct_0(X0_48))
    | k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_2033,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_6,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_144,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | v2_struct_0(k1_tex_2(X0,X1))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_tex_2(X0,X1))
    | k6_domain_1(u1_struct_0(X0),X1) = u1_struct_0(k1_tex_2(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_6])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_tex_2(X1,X0))
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_150,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_145,c_8,c_7])).

cnf(c_151,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k6_domain_1(u1_struct_0(X1),X0) = u1_struct_0(k1_tex_2(X1,X0)) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_973,plain,
    ( ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | k6_domain_1(u1_struct_0(X0_48),X0_47) = u1_struct_0(k1_tex_2(X0_48,X0_47)) ),
    inference(subtyping,[status(esa)],[c_151])).

cnf(c_1998,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | k6_domain_1(u1_struct_0(X0_48),sK0(sK2)) = u1_struct_0(k1_tex_2(X0_48,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2020,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | k6_domain_1(u1_struct_0(sK1),sK0(sK2)) = u1_struct_0(k1_tex_2(sK1,sK0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1998])).

cnf(c_986,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,X0_47),X0_48)
    | ~ m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2000,plain,
    ( m1_pre_topc(k1_tex_2(X0_48,sK0(sK2)),X0_48)
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_2012,plain,
    ( m1_pre_topc(k1_tex_2(sK1,sK0(sK2)),sK1)
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_982,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | m1_subset_1(u1_struct_0(X0_48),k1_zfmisc_1(u1_struct_0(X1_48)))
    | ~ l1_pre_topc(X1_48) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1854,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_48)))
    | ~ l1_pre_topc(X0_48) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_1856,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1854])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_14,c_15])).

cnf(c_972,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | m1_subset_1(X0_47,X2_47)
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(X2_47))
    | v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_271])).

cnf(c_1662,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(X0_48)))
    | m1_subset_1(X0_47,u1_struct_0(X0_48))
    | v1_xboole_0(X1_47) ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_1794,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(X0_48))
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(X0_48)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1662])).

cnf(c_1796,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1794])).

cnf(c_1782,plain,
    ( ~ m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = k1_tarski(sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_981])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_983,plain,
    ( ~ m1_pre_topc(X0_48,X1_48)
    | ~ l1_pre_topc(X1_48)
    | l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1613,plain,
    ( ~ m1_pre_topc(sK2,X0_48)
    | ~ l1_pre_topc(X0_48)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_983])).

cnf(c_1615,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_443,plain,
    ( v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k6_domain_1(u1_struct_0(X0),sK0(X0)) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_2])).

cnf(c_969,plain,
    ( v2_struct_0(X0_48)
    | ~ v7_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48)
    | k6_domain_1(u1_struct_0(X0_48),sK0(X0_48)) = u1_struct_0(X0_48) ),
    inference(subtyping,[status(esa)],[c_443])).

cnf(c_1510,plain,
    ( v2_struct_0(sK2)
    | ~ v7_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k6_domain_1(u1_struct_0(sK2),sK0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_11,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_412,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_11])).

cnf(c_971,plain,
    ( ~ v1_xboole_0(u1_struct_0(X0_48))
    | v2_struct_0(X0_48)
    | ~ l1_pre_topc(X0_48) ),
    inference(subtyping,[status(esa)],[c_412])).

cnf(c_1515,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_971])).

cnf(c_3,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v7_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_426,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v7_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_9,c_3])).

cnf(c_19,negated_conjecture,
    ( v7_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_605,plain,
    ( m1_subset_1(sK0(X0),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_426,c_19])).

cnf(c_606,plain,
    ( m1_subset_1(sK0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_51,plain,
    ( l1_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_47,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12841,c_10835,c_7885,c_6716,c_4809,c_3816,c_3811,c_3776,c_3641,c_3103,c_2368,c_2056,c_2033,c_2020,c_2012,c_1856,c_1796,c_1782,c_1615,c_1510,c_1515,c_606,c_51,c_47,c_18,c_19,c_20,c_21,c_22])).


%------------------------------------------------------------------------------
