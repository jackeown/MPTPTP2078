%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:35 EST 2020

% Result     : Theorem 1.21s
% Output     : CNFRefutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 220 expanded)
%              Number of clauses        :   42 (  54 expanded)
%              Number of leaves         :   12 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  329 (1323 expanded)
%              Number of equality atoms :   54 ( 203 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & r2_hidden(X2,sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f34,f33,f32])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f51,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1346,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1647,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1346])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1349,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | v1_xboole_0(X1_48)
    | k6_domain_1(X1_48,X0_48) = k1_tarski(X0_48) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1645,plain,
    ( k6_domain_1(X0_48,X1_48) = k1_tarski(X1_48)
    | m1_subset_1(X1_48,X0_48) != iProver_top
    | v1_xboole_0(X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1349])).

cnf(c_2130,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1647,c_1645])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_7,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_44,plain,
    ( v2_struct_0(sK2)
    | ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_47,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1770,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_2230,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2130,c_20,c_18,c_15,c_44,c_47,c_1770])).

cnf(c_13,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1348,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_2233,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
    inference(demodulation,[status(thm)],[c_2230,c_1348])).

cnf(c_2,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_155,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k1_tarski(X0),X1) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_156,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_155])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_397,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_398,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_402,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_20,c_18])).

cnf(c_403,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_402])).

cnf(c_597,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X2,X3)
    | X0 != X3
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | k1_tarski(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_156,c_403])).

cnf(c_598,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,k1_tarski(X1))) = k1_tarski(X1) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_1340,plain,
    ( ~ v2_tex_2(X0_48,sK2)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(X1_48),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1_48,X0_48)
    | k9_subset_1(u1_struct_0(sK2),X0_48,k2_pre_topc(sK2,k1_tarski(X1_48))) = k1_tarski(X1_48) ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_1889,plain,
    ( ~ v2_tex_2(X0_48,sK2)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,X0_48)
    | k9_subset_1(u1_struct_0(sK2),X0_48,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_1891,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_4,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1351,plain,
    ( m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X1_48))
    | ~ r2_hidden(X0_48,X1_48) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1814,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1350,plain,
    ( ~ m1_subset_1(X0_48,X1_48)
    | r2_hidden(X0_48,X1_48)
    | v1_xboole_0(X1_48) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1764,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_16,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2233,c_1891,c_1814,c_1764,c_47,c_44,c_14,c_15,c_16,c_17,c_18,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:58:38 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.21/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.21/0.98  
% 1.21/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.21/0.98  
% 1.21/0.98  ------  iProver source info
% 1.21/0.98  
% 1.21/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.21/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.21/0.98  git: non_committed_changes: false
% 1.21/0.98  git: last_make_outside_of_git: false
% 1.21/0.98  
% 1.21/0.98  ------ 
% 1.21/0.98  
% 1.21/0.98  ------ Input Options
% 1.21/0.98  
% 1.21/0.98  --out_options                           all
% 1.21/0.98  --tptp_safe_out                         true
% 1.21/0.98  --problem_path                          ""
% 1.21/0.98  --include_path                          ""
% 1.21/0.98  --clausifier                            res/vclausify_rel
% 1.21/0.98  --clausifier_options                    --mode clausify
% 1.21/0.98  --stdin                                 false
% 1.21/0.98  --stats_out                             all
% 1.21/0.98  
% 1.21/0.98  ------ General Options
% 1.21/0.98  
% 1.21/0.98  --fof                                   false
% 1.21/0.98  --time_out_real                         305.
% 1.21/0.98  --time_out_virtual                      -1.
% 1.21/0.98  --symbol_type_check                     false
% 1.21/0.98  --clausify_out                          false
% 1.21/0.98  --sig_cnt_out                           false
% 1.21/0.98  --trig_cnt_out                          false
% 1.21/0.98  --trig_cnt_out_tolerance                1.
% 1.21/0.98  --trig_cnt_out_sk_spl                   false
% 1.21/0.98  --abstr_cl_out                          false
% 1.21/0.98  
% 1.21/0.98  ------ Global Options
% 1.21/0.98  
% 1.21/0.98  --schedule                              default
% 1.21/0.98  --add_important_lit                     false
% 1.21/0.98  --prop_solver_per_cl                    1000
% 1.21/0.98  --min_unsat_core                        false
% 1.21/0.98  --soft_assumptions                      false
% 1.21/0.98  --soft_lemma_size                       3
% 1.21/0.98  --prop_impl_unit_size                   0
% 1.21/0.98  --prop_impl_unit                        []
% 1.21/0.98  --share_sel_clauses                     true
% 1.21/0.98  --reset_solvers                         false
% 1.21/0.98  --bc_imp_inh                            [conj_cone]
% 1.21/0.98  --conj_cone_tolerance                   3.
% 1.21/0.98  --extra_neg_conj                        none
% 1.21/0.98  --large_theory_mode                     true
% 1.21/0.98  --prolific_symb_bound                   200
% 1.21/0.98  --lt_threshold                          2000
% 1.21/0.98  --clause_weak_htbl                      true
% 1.21/0.98  --gc_record_bc_elim                     false
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing Options
% 1.21/0.98  
% 1.21/0.98  --preprocessing_flag                    true
% 1.21/0.98  --time_out_prep_mult                    0.1
% 1.21/0.98  --splitting_mode                        input
% 1.21/0.98  --splitting_grd                         true
% 1.21/0.98  --splitting_cvd                         false
% 1.21/0.98  --splitting_cvd_svl                     false
% 1.21/0.98  --splitting_nvd                         32
% 1.21/0.98  --sub_typing                            true
% 1.21/0.98  --prep_gs_sim                           true
% 1.21/0.98  --prep_unflatten                        true
% 1.21/0.98  --prep_res_sim                          true
% 1.21/0.98  --prep_upred                            true
% 1.21/0.98  --prep_sem_filter                       exhaustive
% 1.21/0.98  --prep_sem_filter_out                   false
% 1.21/0.98  --pred_elim                             true
% 1.21/0.98  --res_sim_input                         true
% 1.21/0.98  --eq_ax_congr_red                       true
% 1.21/0.98  --pure_diseq_elim                       true
% 1.21/0.98  --brand_transform                       false
% 1.21/0.98  --non_eq_to_eq                          false
% 1.21/0.98  --prep_def_merge                        true
% 1.21/0.98  --prep_def_merge_prop_impl              false
% 1.21/0.98  --prep_def_merge_mbd                    true
% 1.21/0.98  --prep_def_merge_tr_red                 false
% 1.21/0.98  --prep_def_merge_tr_cl                  false
% 1.21/0.98  --smt_preprocessing                     true
% 1.21/0.98  --smt_ac_axioms                         fast
% 1.21/0.98  --preprocessed_out                      false
% 1.21/0.98  --preprocessed_stats                    false
% 1.21/0.98  
% 1.21/0.98  ------ Abstraction refinement Options
% 1.21/0.98  
% 1.21/0.98  --abstr_ref                             []
% 1.21/0.98  --abstr_ref_prep                        false
% 1.21/0.98  --abstr_ref_until_sat                   false
% 1.21/0.98  --abstr_ref_sig_restrict                funpre
% 1.21/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/0.98  --abstr_ref_under                       []
% 1.21/0.98  
% 1.21/0.98  ------ SAT Options
% 1.21/0.98  
% 1.21/0.98  --sat_mode                              false
% 1.21/0.98  --sat_fm_restart_options                ""
% 1.21/0.98  --sat_gr_def                            false
% 1.21/0.98  --sat_epr_types                         true
% 1.21/0.98  --sat_non_cyclic_types                  false
% 1.21/0.98  --sat_finite_models                     false
% 1.21/0.98  --sat_fm_lemmas                         false
% 1.21/0.98  --sat_fm_prep                           false
% 1.21/0.98  --sat_fm_uc_incr                        true
% 1.21/0.98  --sat_out_model                         small
% 1.21/0.98  --sat_out_clauses                       false
% 1.21/0.98  
% 1.21/0.98  ------ QBF Options
% 1.21/0.98  
% 1.21/0.98  --qbf_mode                              false
% 1.21/0.98  --qbf_elim_univ                         false
% 1.21/0.98  --qbf_dom_inst                          none
% 1.21/0.98  --qbf_dom_pre_inst                      false
% 1.21/0.98  --qbf_sk_in                             false
% 1.21/0.98  --qbf_pred_elim                         true
% 1.21/0.98  --qbf_split                             512
% 1.21/0.98  
% 1.21/0.98  ------ BMC1 Options
% 1.21/0.98  
% 1.21/0.98  --bmc1_incremental                      false
% 1.21/0.98  --bmc1_axioms                           reachable_all
% 1.21/0.98  --bmc1_min_bound                        0
% 1.21/0.98  --bmc1_max_bound                        -1
% 1.21/0.98  --bmc1_max_bound_default                -1
% 1.21/0.98  --bmc1_symbol_reachability              true
% 1.21/0.98  --bmc1_property_lemmas                  false
% 1.21/0.98  --bmc1_k_induction                      false
% 1.21/0.98  --bmc1_non_equiv_states                 false
% 1.21/0.98  --bmc1_deadlock                         false
% 1.21/0.98  --bmc1_ucm                              false
% 1.21/0.98  --bmc1_add_unsat_core                   none
% 1.21/0.98  --bmc1_unsat_core_children              false
% 1.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/0.98  --bmc1_out_stat                         full
% 1.21/0.98  --bmc1_ground_init                      false
% 1.21/0.98  --bmc1_pre_inst_next_state              false
% 1.21/0.98  --bmc1_pre_inst_state                   false
% 1.21/0.98  --bmc1_pre_inst_reach_state             false
% 1.21/0.98  --bmc1_out_unsat_core                   false
% 1.21/0.98  --bmc1_aig_witness_out                  false
% 1.21/0.98  --bmc1_verbose                          false
% 1.21/0.98  --bmc1_dump_clauses_tptp                false
% 1.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.21/0.98  --bmc1_dump_file                        -
% 1.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.21/0.98  --bmc1_ucm_extend_mode                  1
% 1.21/0.98  --bmc1_ucm_init_mode                    2
% 1.21/0.98  --bmc1_ucm_cone_mode                    none
% 1.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.21/0.98  --bmc1_ucm_relax_model                  4
% 1.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/0.98  --bmc1_ucm_layered_model                none
% 1.21/0.98  --bmc1_ucm_max_lemma_size               10
% 1.21/0.98  
% 1.21/0.98  ------ AIG Options
% 1.21/0.98  
% 1.21/0.98  --aig_mode                              false
% 1.21/0.98  
% 1.21/0.98  ------ Instantiation Options
% 1.21/0.98  
% 1.21/0.98  --instantiation_flag                    true
% 1.21/0.98  --inst_sos_flag                         false
% 1.21/0.98  --inst_sos_phase                        true
% 1.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/0.98  --inst_lit_sel_side                     num_symb
% 1.21/0.98  --inst_solver_per_active                1400
% 1.21/0.98  --inst_solver_calls_frac                1.
% 1.21/0.98  --inst_passive_queue_type               priority_queues
% 1.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/0.98  --inst_passive_queues_freq              [25;2]
% 1.21/0.98  --inst_dismatching                      true
% 1.21/0.98  --inst_eager_unprocessed_to_passive     true
% 1.21/0.98  --inst_prop_sim_given                   true
% 1.21/0.98  --inst_prop_sim_new                     false
% 1.21/0.98  --inst_subs_new                         false
% 1.21/0.98  --inst_eq_res_simp                      false
% 1.21/0.98  --inst_subs_given                       false
% 1.21/0.98  --inst_orphan_elimination               true
% 1.21/0.98  --inst_learning_loop_flag               true
% 1.21/0.98  --inst_learning_start                   3000
% 1.21/0.98  --inst_learning_factor                  2
% 1.21/0.98  --inst_start_prop_sim_after_learn       3
% 1.21/0.98  --inst_sel_renew                        solver
% 1.21/0.98  --inst_lit_activity_flag                true
% 1.21/0.98  --inst_restr_to_given                   false
% 1.21/0.98  --inst_activity_threshold               500
% 1.21/0.98  --inst_out_proof                        true
% 1.21/0.98  
% 1.21/0.98  ------ Resolution Options
% 1.21/0.98  
% 1.21/0.98  --resolution_flag                       true
% 1.21/0.98  --res_lit_sel                           adaptive
% 1.21/0.98  --res_lit_sel_side                      none
% 1.21/0.98  --res_ordering                          kbo
% 1.21/0.98  --res_to_prop_solver                    active
% 1.21/0.98  --res_prop_simpl_new                    false
% 1.21/0.98  --res_prop_simpl_given                  true
% 1.21/0.98  --res_passive_queue_type                priority_queues
% 1.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/0.98  --res_passive_queues_freq               [15;5]
% 1.21/0.98  --res_forward_subs                      full
% 1.21/0.98  --res_backward_subs                     full
% 1.21/0.98  --res_forward_subs_resolution           true
% 1.21/0.98  --res_backward_subs_resolution          true
% 1.21/0.98  --res_orphan_elimination                true
% 1.21/0.98  --res_time_limit                        2.
% 1.21/0.98  --res_out_proof                         true
% 1.21/0.98  
% 1.21/0.98  ------ Superposition Options
% 1.21/0.98  
% 1.21/0.98  --superposition_flag                    true
% 1.21/0.98  --sup_passive_queue_type                priority_queues
% 1.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.21/0.98  --demod_completeness_check              fast
% 1.21/0.98  --demod_use_ground                      true
% 1.21/0.98  --sup_to_prop_solver                    passive
% 1.21/0.98  --sup_prop_simpl_new                    true
% 1.21/0.98  --sup_prop_simpl_given                  true
% 1.21/0.98  --sup_fun_splitting                     false
% 1.21/0.98  --sup_smt_interval                      50000
% 1.21/0.98  
% 1.21/0.98  ------ Superposition Simplification Setup
% 1.21/0.98  
% 1.21/0.98  --sup_indices_passive                   []
% 1.21/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_full_bw                           [BwDemod]
% 1.21/0.98  --sup_immed_triv                        [TrivRules]
% 1.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_immed_bw_main                     []
% 1.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.98  
% 1.21/0.98  ------ Combination Options
% 1.21/0.98  
% 1.21/0.98  --comb_res_mult                         3
% 1.21/0.98  --comb_sup_mult                         2
% 1.21/0.98  --comb_inst_mult                        10
% 1.21/0.98  
% 1.21/0.98  ------ Debug Options
% 1.21/0.98  
% 1.21/0.98  --dbg_backtrace                         false
% 1.21/0.98  --dbg_dump_prop_clauses                 false
% 1.21/0.98  --dbg_dump_prop_clauses_file            -
% 1.21/0.98  --dbg_out_stat                          false
% 1.21/0.98  ------ Parsing...
% 1.21/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.21/0.98  ------ Proving...
% 1.21/0.98  ------ Problem Properties 
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  clauses                                 15
% 1.21/0.98  conjectures                             5
% 1.21/0.98  EPR                                     4
% 1.21/0.98  Horn                                    10
% 1.21/0.98  unary                                   6
% 1.21/0.98  binary                                  3
% 1.21/0.98  lits                                    33
% 1.21/0.98  lits eq                                 5
% 1.21/0.98  fd_pure                                 0
% 1.21/0.98  fd_pseudo                               0
% 1.21/0.98  fd_cond                                 0
% 1.21/0.98  fd_pseudo_cond                          0
% 1.21/0.98  AC symbols                              0
% 1.21/0.98  
% 1.21/0.98  ------ Schedule dynamic 5 is on 
% 1.21/0.98  
% 1.21/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  ------ 
% 1.21/0.98  Current options:
% 1.21/0.98  ------ 
% 1.21/0.98  
% 1.21/0.98  ------ Input Options
% 1.21/0.98  
% 1.21/0.98  --out_options                           all
% 1.21/0.98  --tptp_safe_out                         true
% 1.21/0.98  --problem_path                          ""
% 1.21/0.98  --include_path                          ""
% 1.21/0.98  --clausifier                            res/vclausify_rel
% 1.21/0.98  --clausifier_options                    --mode clausify
% 1.21/0.98  --stdin                                 false
% 1.21/0.98  --stats_out                             all
% 1.21/0.98  
% 1.21/0.98  ------ General Options
% 1.21/0.98  
% 1.21/0.98  --fof                                   false
% 1.21/0.98  --time_out_real                         305.
% 1.21/0.98  --time_out_virtual                      -1.
% 1.21/0.98  --symbol_type_check                     false
% 1.21/0.98  --clausify_out                          false
% 1.21/0.98  --sig_cnt_out                           false
% 1.21/0.98  --trig_cnt_out                          false
% 1.21/0.98  --trig_cnt_out_tolerance                1.
% 1.21/0.98  --trig_cnt_out_sk_spl                   false
% 1.21/0.98  --abstr_cl_out                          false
% 1.21/0.98  
% 1.21/0.98  ------ Global Options
% 1.21/0.98  
% 1.21/0.98  --schedule                              default
% 1.21/0.98  --add_important_lit                     false
% 1.21/0.98  --prop_solver_per_cl                    1000
% 1.21/0.98  --min_unsat_core                        false
% 1.21/0.98  --soft_assumptions                      false
% 1.21/0.98  --soft_lemma_size                       3
% 1.21/0.98  --prop_impl_unit_size                   0
% 1.21/0.98  --prop_impl_unit                        []
% 1.21/0.98  --share_sel_clauses                     true
% 1.21/0.98  --reset_solvers                         false
% 1.21/0.98  --bc_imp_inh                            [conj_cone]
% 1.21/0.98  --conj_cone_tolerance                   3.
% 1.21/0.98  --extra_neg_conj                        none
% 1.21/0.98  --large_theory_mode                     true
% 1.21/0.98  --prolific_symb_bound                   200
% 1.21/0.98  --lt_threshold                          2000
% 1.21/0.98  --clause_weak_htbl                      true
% 1.21/0.98  --gc_record_bc_elim                     false
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing Options
% 1.21/0.98  
% 1.21/0.98  --preprocessing_flag                    true
% 1.21/0.98  --time_out_prep_mult                    0.1
% 1.21/0.98  --splitting_mode                        input
% 1.21/0.98  --splitting_grd                         true
% 1.21/0.98  --splitting_cvd                         false
% 1.21/0.98  --splitting_cvd_svl                     false
% 1.21/0.98  --splitting_nvd                         32
% 1.21/0.98  --sub_typing                            true
% 1.21/0.98  --prep_gs_sim                           true
% 1.21/0.98  --prep_unflatten                        true
% 1.21/0.98  --prep_res_sim                          true
% 1.21/0.98  --prep_upred                            true
% 1.21/0.98  --prep_sem_filter                       exhaustive
% 1.21/0.98  --prep_sem_filter_out                   false
% 1.21/0.98  --pred_elim                             true
% 1.21/0.98  --res_sim_input                         true
% 1.21/0.98  --eq_ax_congr_red                       true
% 1.21/0.98  --pure_diseq_elim                       true
% 1.21/0.98  --brand_transform                       false
% 1.21/0.98  --non_eq_to_eq                          false
% 1.21/0.98  --prep_def_merge                        true
% 1.21/0.98  --prep_def_merge_prop_impl              false
% 1.21/0.98  --prep_def_merge_mbd                    true
% 1.21/0.98  --prep_def_merge_tr_red                 false
% 1.21/0.98  --prep_def_merge_tr_cl                  false
% 1.21/0.98  --smt_preprocessing                     true
% 1.21/0.98  --smt_ac_axioms                         fast
% 1.21/0.98  --preprocessed_out                      false
% 1.21/0.98  --preprocessed_stats                    false
% 1.21/0.98  
% 1.21/0.98  ------ Abstraction refinement Options
% 1.21/0.98  
% 1.21/0.98  --abstr_ref                             []
% 1.21/0.98  --abstr_ref_prep                        false
% 1.21/0.98  --abstr_ref_until_sat                   false
% 1.21/0.98  --abstr_ref_sig_restrict                funpre
% 1.21/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.21/0.98  --abstr_ref_under                       []
% 1.21/0.98  
% 1.21/0.98  ------ SAT Options
% 1.21/0.98  
% 1.21/0.98  --sat_mode                              false
% 1.21/0.98  --sat_fm_restart_options                ""
% 1.21/0.98  --sat_gr_def                            false
% 1.21/0.98  --sat_epr_types                         true
% 1.21/0.98  --sat_non_cyclic_types                  false
% 1.21/0.98  --sat_finite_models                     false
% 1.21/0.98  --sat_fm_lemmas                         false
% 1.21/0.98  --sat_fm_prep                           false
% 1.21/0.98  --sat_fm_uc_incr                        true
% 1.21/0.98  --sat_out_model                         small
% 1.21/0.98  --sat_out_clauses                       false
% 1.21/0.98  
% 1.21/0.98  ------ QBF Options
% 1.21/0.98  
% 1.21/0.98  --qbf_mode                              false
% 1.21/0.98  --qbf_elim_univ                         false
% 1.21/0.98  --qbf_dom_inst                          none
% 1.21/0.98  --qbf_dom_pre_inst                      false
% 1.21/0.98  --qbf_sk_in                             false
% 1.21/0.98  --qbf_pred_elim                         true
% 1.21/0.98  --qbf_split                             512
% 1.21/0.98  
% 1.21/0.98  ------ BMC1 Options
% 1.21/0.98  
% 1.21/0.98  --bmc1_incremental                      false
% 1.21/0.98  --bmc1_axioms                           reachable_all
% 1.21/0.98  --bmc1_min_bound                        0
% 1.21/0.98  --bmc1_max_bound                        -1
% 1.21/0.98  --bmc1_max_bound_default                -1
% 1.21/0.98  --bmc1_symbol_reachability              true
% 1.21/0.98  --bmc1_property_lemmas                  false
% 1.21/0.98  --bmc1_k_induction                      false
% 1.21/0.98  --bmc1_non_equiv_states                 false
% 1.21/0.98  --bmc1_deadlock                         false
% 1.21/0.98  --bmc1_ucm                              false
% 1.21/0.98  --bmc1_add_unsat_core                   none
% 1.21/0.98  --bmc1_unsat_core_children              false
% 1.21/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.21/0.98  --bmc1_out_stat                         full
% 1.21/0.98  --bmc1_ground_init                      false
% 1.21/0.98  --bmc1_pre_inst_next_state              false
% 1.21/0.98  --bmc1_pre_inst_state                   false
% 1.21/0.98  --bmc1_pre_inst_reach_state             false
% 1.21/0.98  --bmc1_out_unsat_core                   false
% 1.21/0.98  --bmc1_aig_witness_out                  false
% 1.21/0.98  --bmc1_verbose                          false
% 1.21/0.98  --bmc1_dump_clauses_tptp                false
% 1.21/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.21/0.98  --bmc1_dump_file                        -
% 1.21/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.21/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.21/0.98  --bmc1_ucm_extend_mode                  1
% 1.21/0.98  --bmc1_ucm_init_mode                    2
% 1.21/0.98  --bmc1_ucm_cone_mode                    none
% 1.21/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.21/0.98  --bmc1_ucm_relax_model                  4
% 1.21/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.21/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.21/0.98  --bmc1_ucm_layered_model                none
% 1.21/0.98  --bmc1_ucm_max_lemma_size               10
% 1.21/0.98  
% 1.21/0.98  ------ AIG Options
% 1.21/0.98  
% 1.21/0.98  --aig_mode                              false
% 1.21/0.98  
% 1.21/0.98  ------ Instantiation Options
% 1.21/0.98  
% 1.21/0.98  --instantiation_flag                    true
% 1.21/0.98  --inst_sos_flag                         false
% 1.21/0.98  --inst_sos_phase                        true
% 1.21/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.21/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.21/0.98  --inst_lit_sel_side                     none
% 1.21/0.98  --inst_solver_per_active                1400
% 1.21/0.98  --inst_solver_calls_frac                1.
% 1.21/0.98  --inst_passive_queue_type               priority_queues
% 1.21/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.21/0.98  --inst_passive_queues_freq              [25;2]
% 1.21/0.98  --inst_dismatching                      true
% 1.21/0.98  --inst_eager_unprocessed_to_passive     true
% 1.21/0.98  --inst_prop_sim_given                   true
% 1.21/0.98  --inst_prop_sim_new                     false
% 1.21/0.98  --inst_subs_new                         false
% 1.21/0.98  --inst_eq_res_simp                      false
% 1.21/0.98  --inst_subs_given                       false
% 1.21/0.98  --inst_orphan_elimination               true
% 1.21/0.98  --inst_learning_loop_flag               true
% 1.21/0.98  --inst_learning_start                   3000
% 1.21/0.98  --inst_learning_factor                  2
% 1.21/0.98  --inst_start_prop_sim_after_learn       3
% 1.21/0.98  --inst_sel_renew                        solver
% 1.21/0.98  --inst_lit_activity_flag                true
% 1.21/0.98  --inst_restr_to_given                   false
% 1.21/0.98  --inst_activity_threshold               500
% 1.21/0.98  --inst_out_proof                        true
% 1.21/0.98  
% 1.21/0.98  ------ Resolution Options
% 1.21/0.98  
% 1.21/0.98  --resolution_flag                       false
% 1.21/0.98  --res_lit_sel                           adaptive
% 1.21/0.98  --res_lit_sel_side                      none
% 1.21/0.98  --res_ordering                          kbo
% 1.21/0.98  --res_to_prop_solver                    active
% 1.21/0.98  --res_prop_simpl_new                    false
% 1.21/0.98  --res_prop_simpl_given                  true
% 1.21/0.98  --res_passive_queue_type                priority_queues
% 1.21/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.21/0.98  --res_passive_queues_freq               [15;5]
% 1.21/0.98  --res_forward_subs                      full
% 1.21/0.98  --res_backward_subs                     full
% 1.21/0.98  --res_forward_subs_resolution           true
% 1.21/0.98  --res_backward_subs_resolution          true
% 1.21/0.98  --res_orphan_elimination                true
% 1.21/0.98  --res_time_limit                        2.
% 1.21/0.98  --res_out_proof                         true
% 1.21/0.98  
% 1.21/0.98  ------ Superposition Options
% 1.21/0.98  
% 1.21/0.98  --superposition_flag                    true
% 1.21/0.98  --sup_passive_queue_type                priority_queues
% 1.21/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.21/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.21/0.98  --demod_completeness_check              fast
% 1.21/0.98  --demod_use_ground                      true
% 1.21/0.98  --sup_to_prop_solver                    passive
% 1.21/0.98  --sup_prop_simpl_new                    true
% 1.21/0.98  --sup_prop_simpl_given                  true
% 1.21/0.98  --sup_fun_splitting                     false
% 1.21/0.98  --sup_smt_interval                      50000
% 1.21/0.98  
% 1.21/0.98  ------ Superposition Simplification Setup
% 1.21/0.98  
% 1.21/0.98  --sup_indices_passive                   []
% 1.21/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.21/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.21/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_full_bw                           [BwDemod]
% 1.21/0.98  --sup_immed_triv                        [TrivRules]
% 1.21/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.21/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_immed_bw_main                     []
% 1.21/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.21/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.21/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.21/0.98  
% 1.21/0.98  ------ Combination Options
% 1.21/0.98  
% 1.21/0.98  --comb_res_mult                         3
% 1.21/0.98  --comb_sup_mult                         2
% 1.21/0.98  --comb_inst_mult                        10
% 1.21/0.98  
% 1.21/0.98  ------ Debug Options
% 1.21/0.98  
% 1.21/0.98  --dbg_backtrace                         false
% 1.21/0.98  --dbg_dump_prop_clauses                 false
% 1.21/0.98  --dbg_dump_prop_clauses_file            -
% 1.21/0.98  --dbg_out_stat                          false
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  ------ Proving...
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  % SZS status Theorem for theBenchmark.p
% 1.21/0.98  
% 1.21/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.21/0.98  
% 1.21/0.98  fof(f9,conjecture,(
% 1.21/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f10,negated_conjecture,(
% 1.21/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 1.21/0.98    inference(negated_conjecture,[],[f9])).
% 1.21/0.98  
% 1.21/0.98  fof(f21,plain,(
% 1.21/0.98    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.21/0.98    inference(ennf_transformation,[],[f10])).
% 1.21/0.98  
% 1.21/0.98  fof(f22,plain,(
% 1.21/0.98    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.21/0.98    inference(flattening,[],[f21])).
% 1.21/0.98  
% 1.21/0.98  fof(f34,plain,(
% 1.21/0.98    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 1.21/0.98    introduced(choice_axiom,[])).
% 1.21/0.98  
% 1.21/0.98  fof(f33,plain,(
% 1.21/0.98    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.21/0.98    introduced(choice_axiom,[])).
% 1.21/0.98  
% 1.21/0.98  fof(f32,plain,(
% 1.21/0.98    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 1.21/0.98    introduced(choice_axiom,[])).
% 1.21/0.98  
% 1.21/0.98  fof(f35,plain,(
% 1.21/0.98    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 1.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f34,f33,f32])).
% 1.21/0.98  
% 1.21/0.98  fof(f54,plain,(
% 1.21/0.98    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f7,axiom,(
% 1.21/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f17,plain,(
% 1.21/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.21/0.98    inference(ennf_transformation,[],[f7])).
% 1.21/0.98  
% 1.21/0.98  fof(f18,plain,(
% 1.21/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.21/0.98    inference(flattening,[],[f17])).
% 1.21/0.98  
% 1.21/0.98  fof(f44,plain,(
% 1.21/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f18])).
% 1.21/0.98  
% 1.21/0.98  fof(f49,plain,(
% 1.21/0.98    ~v2_struct_0(sK2)),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f51,plain,(
% 1.21/0.98    l1_pre_topc(sK2)),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f6,axiom,(
% 1.21/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f15,plain,(
% 1.21/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.21/0.98    inference(ennf_transformation,[],[f6])).
% 1.21/0.98  
% 1.21/0.98  fof(f16,plain,(
% 1.21/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.21/0.98    inference(flattening,[],[f15])).
% 1.21/0.98  
% 1.21/0.98  fof(f43,plain,(
% 1.21/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f16])).
% 1.21/0.98  
% 1.21/0.98  fof(f5,axiom,(
% 1.21/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f14,plain,(
% 1.21/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.21/0.98    inference(ennf_transformation,[],[f5])).
% 1.21/0.98  
% 1.21/0.98  fof(f42,plain,(
% 1.21/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f14])).
% 1.21/0.98  
% 1.21/0.98  fof(f56,plain,(
% 1.21/0.98    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f2,axiom,(
% 1.21/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f27,plain,(
% 1.21/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.21/0.98    inference(nnf_transformation,[],[f2])).
% 1.21/0.98  
% 1.21/0.98  fof(f39,plain,(
% 1.21/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f27])).
% 1.21/0.98  
% 1.21/0.98  fof(f8,axiom,(
% 1.21/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f19,plain,(
% 1.21/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.21/0.98    inference(ennf_transformation,[],[f8])).
% 1.21/0.98  
% 1.21/0.98  fof(f20,plain,(
% 1.21/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.98    inference(flattening,[],[f19])).
% 1.21/0.98  
% 1.21/0.98  fof(f28,plain,(
% 1.21/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.98    inference(nnf_transformation,[],[f20])).
% 1.21/0.98  
% 1.21/0.98  fof(f29,plain,(
% 1.21/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.98    inference(rectify,[],[f28])).
% 1.21/0.98  
% 1.21/0.98  fof(f30,plain,(
% 1.21/0.98    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.21/0.98    introduced(choice_axiom,[])).
% 1.21/0.98  
% 1.21/0.98  fof(f31,plain,(
% 1.21/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.21/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 1.21/0.98  
% 1.21/0.98  fof(f45,plain,(
% 1.21/0.98    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f31])).
% 1.21/0.98  
% 1.21/0.98  fof(f50,plain,(
% 1.21/0.98    v2_pre_topc(sK2)),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f3,axiom,(
% 1.21/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f11,plain,(
% 1.21/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.21/0.98    inference(ennf_transformation,[],[f3])).
% 1.21/0.98  
% 1.21/0.98  fof(f40,plain,(
% 1.21/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f11])).
% 1.21/0.98  
% 1.21/0.98  fof(f4,axiom,(
% 1.21/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.21/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.21/0.98  
% 1.21/0.98  fof(f12,plain,(
% 1.21/0.98    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.21/0.98    inference(ennf_transformation,[],[f4])).
% 1.21/0.98  
% 1.21/0.98  fof(f13,plain,(
% 1.21/0.98    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.21/0.98    inference(flattening,[],[f12])).
% 1.21/0.98  
% 1.21/0.98  fof(f41,plain,(
% 1.21/0.98    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.21/0.98    inference(cnf_transformation,[],[f13])).
% 1.21/0.98  
% 1.21/0.98  fof(f55,plain,(
% 1.21/0.98    r2_hidden(sK4,sK3)),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f53,plain,(
% 1.21/0.98    v2_tex_2(sK3,sK2)),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  fof(f52,plain,(
% 1.21/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.21/0.98    inference(cnf_transformation,[],[f35])).
% 1.21/0.98  
% 1.21/0.98  cnf(c_15,negated_conjecture,
% 1.21/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.21/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1346,negated_conjecture,
% 1.21/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1647,plain,
% 1.21/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 1.21/0.98      inference(predicate_to_equality,[status(thm)],[c_1346]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_8,plain,
% 1.21/0.98      ( ~ m1_subset_1(X0,X1)
% 1.21/0.98      | v1_xboole_0(X1)
% 1.21/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 1.21/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1349,plain,
% 1.21/0.98      ( ~ m1_subset_1(X0_48,X1_48)
% 1.21/0.98      | v1_xboole_0(X1_48)
% 1.21/0.98      | k6_domain_1(X1_48,X0_48) = k1_tarski(X0_48) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_8]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1645,plain,
% 1.21/0.98      ( k6_domain_1(X0_48,X1_48) = k1_tarski(X1_48)
% 1.21/0.98      | m1_subset_1(X1_48,X0_48) != iProver_top
% 1.21/0.98      | v1_xboole_0(X0_48) = iProver_top ),
% 1.21/0.98      inference(predicate_to_equality,[status(thm)],[c_1349]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_2130,plain,
% 1.21/0.98      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
% 1.21/0.98      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 1.21/0.98      inference(superposition,[status(thm)],[c_1647,c_1645]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_20,negated_conjecture,
% 1.21/0.98      ( ~ v2_struct_0(sK2) ),
% 1.21/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_18,negated_conjecture,
% 1.21/0.98      ( l1_pre_topc(sK2) ),
% 1.21/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_7,plain,
% 1.21/0.98      ( v2_struct_0(X0)
% 1.21/0.98      | ~ l1_struct_0(X0)
% 1.21/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 1.21/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_44,plain,
% 1.21/0.98      ( v2_struct_0(sK2)
% 1.21/0.98      | ~ l1_struct_0(sK2)
% 1.21/0.98      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_6,plain,
% 1.21/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 1.21/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_47,plain,
% 1.21/0.98      ( ~ l1_pre_topc(sK2) | l1_struct_0(sK2) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1770,plain,
% 1.21/0.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.21/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 1.21/0.98      | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_1349]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_2230,plain,
% 1.21/0.98      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 1.21/0.98      inference(global_propositional_subsumption,
% 1.21/0.98                [status(thm)],
% 1.21/0.98                [c_2130,c_20,c_18,c_15,c_44,c_47,c_1770]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_13,negated_conjecture,
% 1.21/0.98      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 1.21/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1348,negated_conjecture,
% 1.21/0.98      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_13]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_2233,plain,
% 1.21/0.98      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
% 1.21/0.98      inference(demodulation,[status(thm)],[c_2230,c_1348]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_2,plain,
% 1.21/0.98      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.21/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_155,plain,
% 1.21/0.98      ( ~ r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1) ),
% 1.21/0.98      inference(prop_impl,[status(thm)],[c_2]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_156,plain,
% 1.21/0.98      ( r1_tarski(k1_tarski(X0),X1) | ~ r2_hidden(X0,X1) ),
% 1.21/0.98      inference(renaming,[status(thm)],[c_155]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_12,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,X1)
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/0.98      | ~ r1_tarski(X2,X0)
% 1.21/0.98      | ~ v2_pre_topc(X1)
% 1.21/0.98      | v2_struct_0(X1)
% 1.21/0.98      | ~ l1_pre_topc(X1)
% 1.21/0.98      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 1.21/0.98      inference(cnf_transformation,[],[f45]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_19,negated_conjecture,
% 1.21/0.98      ( v2_pre_topc(sK2) ),
% 1.21/0.98      inference(cnf_transformation,[],[f50]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_397,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,X1)
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.21/0.98      | ~ r1_tarski(X2,X0)
% 1.21/0.98      | v2_struct_0(X1)
% 1.21/0.98      | ~ l1_pre_topc(X1)
% 1.21/0.98      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 1.21/0.98      | sK2 != X1 ),
% 1.21/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_398,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,sK2)
% 1.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r1_tarski(X1,X0)
% 1.21/0.98      | v2_struct_0(sK2)
% 1.21/0.98      | ~ l1_pre_topc(sK2)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 1.21/0.98      inference(unflattening,[status(thm)],[c_397]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_402,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,sK2)
% 1.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r1_tarski(X1,X0)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 1.21/0.98      inference(global_propositional_subsumption,
% 1.21/0.98                [status(thm)],
% 1.21/0.98                [c_398,c_20,c_18]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_403,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,sK2)
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r1_tarski(X1,X0)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 1.21/0.98      inference(renaming,[status(thm)],[c_402]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_597,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,sK2)
% 1.21/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(X2,X3)
% 1.21/0.98      | X0 != X3
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 1.21/0.98      | k1_tarski(X2) != X1 ),
% 1.21/0.98      inference(resolution_lifted,[status(thm)],[c_156,c_403]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_598,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0,sK2)
% 1.21/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(k1_tarski(X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(X1,X0)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,k1_tarski(X1))) = k1_tarski(X1) ),
% 1.21/0.98      inference(unflattening,[status(thm)],[c_597]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1340,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0_48,sK2)
% 1.21/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(k1_tarski(X1_48),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(X1_48,X0_48)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0_48,k2_pre_topc(sK2,k1_tarski(X1_48))) = k1_tarski(X1_48) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_598]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1889,plain,
% 1.21/0.98      ( ~ v2_tex_2(X0_48,sK2)
% 1.21/0.98      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(sK4,X0_48)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),X0_48,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_1340]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1891,plain,
% 1.21/0.98      ( ~ v2_tex_2(sK3,sK2)
% 1.21/0.98      | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(sK4,sK3)
% 1.21/0.98      | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_1889]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_4,plain,
% 1.21/0.98      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 1.21/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1351,plain,
% 1.21/0.98      ( m1_subset_1(k1_tarski(X0_48),k1_zfmisc_1(X1_48))
% 1.21/0.98      | ~ r2_hidden(X0_48,X1_48) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1814,plain,
% 1.21/0.98      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.21/0.98      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_1351]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_5,plain,
% 1.21/0.98      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.21/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1350,plain,
% 1.21/0.98      ( ~ m1_subset_1(X0_48,X1_48)
% 1.21/0.98      | r2_hidden(X0_48,X1_48)
% 1.21/0.98      | v1_xboole_0(X1_48) ),
% 1.21/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_1764,plain,
% 1.21/0.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 1.21/0.98      | r2_hidden(sK4,u1_struct_0(sK2))
% 1.21/0.98      | v1_xboole_0(u1_struct_0(sK2)) ),
% 1.21/0.98      inference(instantiation,[status(thm)],[c_1350]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_14,negated_conjecture,
% 1.21/0.98      ( r2_hidden(sK4,sK3) ),
% 1.21/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_16,negated_conjecture,
% 1.21/0.98      ( v2_tex_2(sK3,sK2) ),
% 1.21/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(c_17,negated_conjecture,
% 1.21/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.21/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.21/0.98  
% 1.21/0.98  cnf(contradiction,plain,
% 1.21/0.98      ( $false ),
% 1.21/0.98      inference(minisat,
% 1.21/0.98                [status(thm)],
% 1.21/0.98                [c_2233,c_1891,c_1814,c_1764,c_47,c_44,c_14,c_15,c_16,
% 1.21/0.98                 c_17,c_18,c_20]) ).
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.21/0.98  
% 1.21/0.98  ------                               Statistics
% 1.21/0.98  
% 1.21/0.98  ------ General
% 1.21/0.98  
% 1.21/0.98  abstr_ref_over_cycles:                  0
% 1.21/0.98  abstr_ref_under_cycles:                 0
% 1.21/0.98  gc_basic_clause_elim:                   0
% 1.21/0.98  forced_gc_time:                         0
% 1.21/0.98  parsing_time:                           0.008
% 1.21/0.98  unif_index_cands_time:                  0.
% 1.21/0.98  unif_index_add_time:                    0.
% 1.21/0.98  orderings_time:                         0.
% 1.21/0.98  out_proof_time:                         0.009
% 1.21/0.98  total_time:                             0.087
% 1.21/0.98  num_of_symbols:                         54
% 1.21/0.98  num_of_terms:                           1518
% 1.21/0.98  
% 1.21/0.98  ------ Preprocessing
% 1.21/0.98  
% 1.21/0.98  num_of_splits:                          0
% 1.21/0.98  num_of_split_atoms:                     0
% 1.21/0.98  num_of_reused_defs:                     0
% 1.21/0.98  num_eq_ax_congr_red:                    16
% 1.21/0.98  num_of_sem_filtered_clauses:            1
% 1.21/0.98  num_of_subtypes:                        3
% 1.21/0.98  monotx_restored_types:                  0
% 1.21/0.98  sat_num_of_epr_types:                   0
% 1.21/0.98  sat_num_of_non_cyclic_types:            0
% 1.21/0.98  sat_guarded_non_collapsed_types:        0
% 1.21/0.98  num_pure_diseq_elim:                    0
% 1.21/0.98  simp_replaced_by:                       0
% 1.21/0.98  res_preprocessed:                       89
% 1.21/0.98  prep_upred:                             0
% 1.21/0.98  prep_unflattend:                        60
% 1.21/0.98  smt_new_axioms:                         0
% 1.21/0.98  pred_elim_cands:                        4
% 1.21/0.98  pred_elim:                              5
% 1.21/0.98  pred_elim_cl:                           6
% 1.21/0.98  pred_elim_cycles:                       12
% 1.21/0.98  merged_defs:                            2
% 1.21/0.98  merged_defs_ncl:                        0
% 1.21/0.98  bin_hyper_res:                          2
% 1.21/0.98  prep_cycles:                            4
% 1.21/0.98  pred_elim_time:                         0.017
% 1.21/0.98  splitting_time:                         0.
% 1.21/0.98  sem_filter_time:                        0.
% 1.21/0.98  monotx_time:                            0.
% 1.21/0.98  subtype_inf_time:                       0.
% 1.21/0.98  
% 1.21/0.98  ------ Problem properties
% 1.21/0.98  
% 1.21/0.98  clauses:                                15
% 1.21/0.98  conjectures:                            5
% 1.21/0.98  epr:                                    4
% 1.21/0.98  horn:                                   10
% 1.21/0.98  ground:                                 6
% 1.21/0.98  unary:                                  6
% 1.21/0.98  binary:                                 3
% 1.21/0.98  lits:                                   33
% 1.21/0.98  lits_eq:                                5
% 1.21/0.98  fd_pure:                                0
% 1.21/0.98  fd_pseudo:                              0
% 1.21/0.98  fd_cond:                                0
% 1.21/0.98  fd_pseudo_cond:                         0
% 1.21/0.98  ac_symbols:                             0
% 1.21/0.98  
% 1.21/0.98  ------ Propositional Solver
% 1.21/0.98  
% 1.21/0.98  prop_solver_calls:                      25
% 1.21/0.98  prop_fast_solver_calls:                 667
% 1.21/0.98  smt_solver_calls:                       0
% 1.21/0.98  smt_fast_solver_calls:                  0
% 1.21/0.98  prop_num_of_clauses:                    483
% 1.21/0.98  prop_preprocess_simplified:             2713
% 1.21/0.98  prop_fo_subsumed:                       17
% 1.21/0.98  prop_solver_time:                       0.
% 1.21/0.98  smt_solver_time:                        0.
% 1.21/0.98  smt_fast_solver_time:                   0.
% 1.21/0.98  prop_fast_solver_time:                  0.
% 1.21/0.98  prop_unsat_core_time:                   0.
% 1.21/0.98  
% 1.21/0.98  ------ QBF
% 1.21/0.98  
% 1.21/0.98  qbf_q_res:                              0
% 1.21/0.98  qbf_num_tautologies:                    0
% 1.21/0.98  qbf_prep_cycles:                        0
% 1.21/0.98  
% 1.21/0.98  ------ BMC1
% 1.21/0.98  
% 1.21/0.98  bmc1_current_bound:                     -1
% 1.21/0.98  bmc1_last_solved_bound:                 -1
% 1.21/0.98  bmc1_unsat_core_size:                   -1
% 1.21/0.98  bmc1_unsat_core_parents_size:           -1
% 1.21/0.98  bmc1_merge_next_fun:                    0
% 1.21/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.21/0.98  
% 1.21/0.98  ------ Instantiation
% 1.21/0.98  
% 1.21/0.98  inst_num_of_clauses:                    116
% 1.21/0.98  inst_num_in_passive:                    21
% 1.21/0.98  inst_num_in_active:                     78
% 1.21/0.98  inst_num_in_unprocessed:                17
% 1.21/0.98  inst_num_of_loops:                      80
% 1.21/0.98  inst_num_of_learning_restarts:          0
% 1.21/0.98  inst_num_moves_active_passive:          0
% 1.21/0.98  inst_lit_activity:                      0
% 1.21/0.98  inst_lit_activity_moves:                0
% 1.21/0.98  inst_num_tautologies:                   0
% 1.21/0.98  inst_num_prop_implied:                  0
% 1.21/0.98  inst_num_existing_simplified:           0
% 1.21/0.98  inst_num_eq_res_simplified:             0
% 1.21/0.98  inst_num_child_elim:                    0
% 1.21/0.98  inst_num_of_dismatching_blockings:      7
% 1.21/0.98  inst_num_of_non_proper_insts:           82
% 1.21/0.98  inst_num_of_duplicates:                 0
% 1.21/0.98  inst_inst_num_from_inst_to_res:         0
% 1.21/0.98  inst_dismatching_checking_time:         0.
% 1.21/0.98  
% 1.21/0.98  ------ Resolution
% 1.21/0.98  
% 1.21/0.98  res_num_of_clauses:                     0
% 1.21/0.98  res_num_in_passive:                     0
% 1.21/0.98  res_num_in_active:                      0
% 1.21/0.98  res_num_of_loops:                       93
% 1.21/0.98  res_forward_subset_subsumed:            2
% 1.21/0.98  res_backward_subset_subsumed:           0
% 1.21/0.98  res_forward_subsumed:                   0
% 1.21/0.98  res_backward_subsumed:                  0
% 1.21/0.98  res_forward_subsumption_resolution:     0
% 1.21/0.98  res_backward_subsumption_resolution:    0
% 1.21/0.98  res_clause_to_clause_subsumption:       59
% 1.21/0.98  res_orphan_elimination:                 0
% 1.21/0.98  res_tautology_del:                      25
% 1.21/0.98  res_num_eq_res_simplified:              0
% 1.21/0.98  res_num_sel_changes:                    0
% 1.21/0.98  res_moves_from_active_to_pass:          0
% 1.21/0.98  
% 1.21/0.98  ------ Superposition
% 1.21/0.98  
% 1.21/0.98  sup_time_total:                         0.
% 1.21/0.98  sup_time_generating:                    0.
% 1.21/0.98  sup_time_sim_full:                      0.
% 1.21/0.98  sup_time_sim_immed:                     0.
% 1.21/0.98  
% 1.21/0.98  sup_num_of_clauses:                     24
% 1.21/0.98  sup_num_in_active:                      14
% 1.21/0.98  sup_num_in_passive:                     10
% 1.21/0.98  sup_num_of_loops:                       15
% 1.21/0.98  sup_fw_superposition:                   10
% 1.21/0.98  sup_bw_superposition:                   1
% 1.21/0.98  sup_immediate_simplified:               0
% 1.21/0.98  sup_given_eliminated:                   0
% 1.21/0.98  comparisons_done:                       0
% 1.21/0.98  comparisons_avoided:                    0
% 1.21/0.98  
% 1.21/0.98  ------ Simplifications
% 1.21/0.98  
% 1.21/0.98  
% 1.21/0.98  sim_fw_subset_subsumed:                 0
% 1.21/0.98  sim_bw_subset_subsumed:                 0
% 1.21/0.98  sim_fw_subsumed:                        0
% 1.21/0.98  sim_bw_subsumed:                        0
% 1.21/0.98  sim_fw_subsumption_res:                 0
% 1.21/0.98  sim_bw_subsumption_res:                 0
% 1.21/0.98  sim_tautology_del:                      1
% 1.21/0.98  sim_eq_tautology_del:                   0
% 1.21/0.98  sim_eq_res_simp:                        0
% 1.21/0.98  sim_fw_demodulated:                     0
% 1.21/0.98  sim_bw_demodulated:                     1
% 1.21/0.98  sim_light_normalised:                   0
% 1.21/0.98  sim_joinable_taut:                      0
% 1.21/0.98  sim_joinable_simp:                      0
% 1.21/0.98  sim_ac_normalised:                      0
% 1.21/0.98  sim_smt_subsumption:                    0
% 1.21/0.98  
%------------------------------------------------------------------------------
