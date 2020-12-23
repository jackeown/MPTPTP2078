%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:42 EST 2020

% Result     : Theorem 23.49s
% Output     : CNFRefutation 23.49s
% Verified   : 
% Statistics : Number of formulae       :  331 (26462 expanded)
%              Number of clauses        :  217 (7152 expanded)
%              Number of leaves         :   29 (5666 expanded)
%              Depth                    :   38
%              Number of atoms          : 1082 (121271 expanded)
%              Number of equality atoms :  492 (14605 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | ~ v1_tex_2(k1_tex_2(X0,X1),X0) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            | v1_tex_2(k1_tex_2(X0,X1),X0) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | ~ v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0))
          | v1_tex_2(k1_tex_2(X0,sK4),X0) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
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
          ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | ~ v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3))
            | v1_tex_2(k1_tex_2(sK3,X1),sK3) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) )
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f69,f71,f70])).

fof(f110,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f108,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f89,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f102,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f16,axiom,(
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

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK2(X0,X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK2(X0,X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f21,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f112,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f59,f60])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f120,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f116])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f117,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f93,f79])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f20,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_zfmisc_1(X0)
          | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ v1_subset_1(k6_domain_1(X0,X1),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) ),
    inference(cnf_transformation,[],[f72])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f98,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v7_struct_0(k1_tex_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f118,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f115])).

fof(f119,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f118])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v7_struct_0(X0)
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f95])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1504,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1526,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2940,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1526])).

cnf(c_38,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_39,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_40,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_90,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_92,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_15,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_94,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_96,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_struct_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_1980,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[status(thm)],[c_10,c_36])).

cnf(c_1981,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1980])).

cnf(c_3061,plain,
    ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2940,c_39,c_40,c_92,c_96,c_1981])).

cnf(c_27,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1511,plain,
    ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1515,plain,
    ( sK2(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6453,plain,
    ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
    | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1515])).

cnf(c_32,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_6,plain,
    ( v1_zfmisc_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_379,plain,
    ( v1_zfmisc_1(X0)
    | ~ m1_subset_1(X1,X0)
    | v1_subset_1(k6_domain_1(X0,X1),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_32,c_6])).

cnf(c_380,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | v1_zfmisc_1(X0) ),
    inference(renaming,[status(thm)],[c_379])).

cnf(c_1500,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_34,negated_conjecture,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1506,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2615,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1506])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3054,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2615,c_41])).

cnf(c_36181,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6453,c_3054])).

cnf(c_38133,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_36181,c_39,c_40,c_41])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | sK1(X0,X1) = X0
    | k2_tarski(X0,X0) = X1 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1532,plain,
    ( sK1(X0,X1) = X0
    | k2_tarski(X0,X0) = X1
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1530,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3933,plain,
    ( sK1(X0,k2_tarski(X1,X1)) = X0
    | sK1(X0,k2_tarski(X1,X1)) = X1
    | k2_tarski(X1,X1) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_1532,c_1530])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1518,plain,
    ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3753,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1518])).

cnf(c_91,plain,
    ( v2_struct_0(sK3)
    | ~ l1_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_95,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1908,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X1))
    | k6_domain_1(u1_struct_0(X1),X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2184,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_4253,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3753,c_38,c_37,c_36,c_91,c_95,c_2184])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4268,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4253,c_1519])).

cnf(c_5067,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4268,c_39,c_40,c_41,c_92,c_96])).

cnf(c_16893,plain,
    ( sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_5067])).

cnf(c_25,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1513,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18875,plain,
    ( sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | k2_tarski(X0,X0) = u1_struct_0(sK3)
    | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16893,c_1513])).

cnf(c_31,plain,
    ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
    | ~ m1_subset_1(X1,X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1508,plain,
    ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_zfmisc_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5110,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4253,c_1508])).

cnf(c_6057,plain,
    ( v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5110,c_39,c_40,c_41,c_92,c_96])).

cnf(c_6058,plain,
    ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6057])).

cnf(c_16892,plain,
    ( sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_6058])).

cnf(c_33450,plain,
    ( sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | k2_tarski(X0,X0) = u1_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18875,c_16892])).

cnf(c_38140,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | k2_tarski(X0,X0) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_38133,c_33450])).

cnf(c_35,negated_conjecture,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1505,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4256,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4253,c_1505])).

cnf(c_38979,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | sK1(sK4,k2_tarski(sK4,sK4)) = sK4
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_38140,c_4256])).

cnf(c_1915,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1916,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1915])).

cnf(c_2053,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ l1_pre_topc(sK3)
    | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_2060,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2053])).

cnf(c_40370,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_38979,c_39,c_40,c_41,c_1916,c_2060])).

cnf(c_40371,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_40370])).

cnf(c_3965,plain,
    ( k6_domain_1(X0,X1) = X0
    | v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1513])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1535,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_356,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_1])).

cnf(c_357,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_1501,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_2774,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_1501])).

cnf(c_6988,plain,
    ( k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_1518])).

cnf(c_1534,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3066,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3061,c_1534])).

cnf(c_8432,plain,
    ( k2_tarski(sK0(u1_struct_0(sK3)),sK0(u1_struct_0(sK3))) = k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_6988,c_3066])).

cnf(c_4257,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4253,c_1506])).

cnf(c_16897,plain,
    ( sK1(X0,k2_tarski(sK4,sK4)) = X0
    | sK1(X0,k2_tarski(sK4,sK4)) = sK4
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3933,c_4257])).

cnf(c_18603,plain,
    ( sK1(sK0(u1_struct_0(sK3)),k2_tarski(sK4,sK4)) = sK0(u1_struct_0(sK3))
    | sK1(sK0(u1_struct_0(sK3)),k2_tarski(sK4,sK4)) = sK4
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8432,c_16897])).

cnf(c_1995,plain,
    ( r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0))
    | v1_xboole_0(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1996,plain,
    ( r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

cnf(c_1998,plain,
    ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_1890,plain,
    ( m1_subset_1(X0,u1_struct_0(X1))
    | ~ r2_hidden(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_2122,plain,
    ( m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X0))
    | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_2123,plain,
    ( m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2122])).

cnf(c_2125,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2123])).

cnf(c_5810,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ v1_zfmisc_1(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_5811,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5810])).

cnf(c_21984,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18603,c_39,c_40,c_41,c_92,c_96,c_1998,c_2125,c_2615,c_5811])).

cnf(c_21990,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3965,c_21984])).

cnf(c_44328,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21990,c_39,c_40,c_92,c_96,c_1998,c_2125])).

cnf(c_44334,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_40371,c_44328])).

cnf(c_8482,plain,
    ( sK0(u1_struct_0(sK3)) = X0
    | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8432,c_1530])).

cnf(c_44694,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | sK0(u1_struct_0(sK3)) = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_44334,c_8482])).

cnf(c_45029,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
    | sK0(u1_struct_0(sK3)) = sK4 ),
    inference(superposition,[status(thm)],[c_3061,c_44694])).

cnf(c_23,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1514,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6643,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,sK2(X1,X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1524])).

cnf(c_45154,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | r2_hidden(sK0(sK2(X1,X0)),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_xboole_0(sK2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_6643])).

cnf(c_86279,plain,
    ( sK0(u1_struct_0(sK3)) = sK4
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK2(sK3,k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_45029,c_45154])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2055,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2056,plain,
    ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2055])).

cnf(c_2041,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(X1))
    | r2_hidden(sK0(u1_struct_0(X0)),X1)
    | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2598,plain,
    ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
    | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2041])).

cnf(c_2599,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
    | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2598])).

cnf(c_3050,plain,
    ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_3051,plain,
    ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3050])).

cnf(c_4418,plain,
    ( v2_struct_0(k1_tex_2(sK3,sK4))
    | ~ l1_struct_0(k1_tex_2(sK3,sK4))
    | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4419,plain,
    ( v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4418])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_3791,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_tex_2(X1,X0)) ),
    inference(resolution,[status(thm)],[c_16,c_27])).

cnf(c_4025,plain,
    ( v2_struct_0(sK3)
    | l1_pre_topc(k1_tex_2(sK3,sK4))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[status(thm)],[c_3791,c_36])).

cnf(c_4491,plain,
    ( l1_pre_topc(k1_tex_2(sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4025,c_38,c_37])).

cnf(c_4503,plain,
    ( l1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(resolution,[status(thm)],[c_4491,c_15])).

cnf(c_4504,plain,
    ( l1_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4503])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tex_2(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1510,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k1_tex_2(X1,X0)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5639,plain,
    ( v2_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1510])).

cnf(c_87361,plain,
    ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_86279,c_39,c_40,c_41,c_1916,c_2056,c_2599,c_3051,c_4419,c_4504,c_5639])).

cnf(c_6644,plain,
    ( sK2(X0,X1) = u1_struct_0(X0)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1514,c_1513])).

cnf(c_21,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK2(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1516,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_subset_1(sK2(X1,X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_49175,plain,
    ( sK2(X0,X1) = u1_struct_0(X0)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6644,c_1516])).

cnf(c_49177,plain,
    ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(X0)
    | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_49175])).

cnf(c_91487,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_49177,c_3054])).

cnf(c_91556,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91487,c_39,c_40,c_41])).

cnf(c_5075,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
    | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5067,c_1513])).

cnf(c_6429,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
    | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_6058])).

cnf(c_91565,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | k2_tarski(sK4,sK4) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_91556,c_6429])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | v7_struct_0(k1_tex_2(X1,X0))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1900,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v7_struct_0(k1_tex_2(sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1901,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
    | v7_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_1517,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4201,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_1513])).

cnf(c_47276,plain,
    ( sK0(u1_struct_0(sK3)) = sK4
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_45029,c_1516])).

cnf(c_119,plain,
    ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_122,plain,
    ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_690,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_703,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_687,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3093,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | X0 != u1_struct_0(k1_tex_2(sK3,sK4))
    | X1 != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_4546,plain,
    ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),X0)
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | X0 != u1_struct_0(sK3)
    | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_6967,plain,
    ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(X0))
    | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
    | u1_struct_0(X0) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_4546])).

cnf(c_6968,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(X0)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6967])).

cnf(c_6970,plain,
    ( sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
    | u1_struct_0(sK3) != u1_struct_0(sK3)
    | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6968])).

cnf(c_10967,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | ~ v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_10968,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10967])).

cnf(c_47307,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47276,c_39,c_40,c_41,c_119,c_122,c_703,c_1916,c_2060,c_6970,c_10968])).

cnf(c_47308,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_47307])).

cnf(c_47314,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4201,c_47308])).

cnf(c_47963,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_47314,c_39,c_40,c_41,c_1916])).

cnf(c_6431,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
    | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5075,c_4257])).

cnf(c_47972,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
    | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_47963,c_6431])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1528,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_33,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v7_struct_0(X0)
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1507,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3721,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v7_struct_0(X1) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1507])).

cnf(c_9155,plain,
    ( v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1528,c_3721])).

cnf(c_9157,plain,
    ( v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2774,c_3721])).

cnf(c_9178,plain,
    ( v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9155,c_9157])).

cnf(c_9184,plain,
    ( v7_struct_0(X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_9178,c_9157])).

cnf(c_90840,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
    | v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_47972,c_9184])).

cnf(c_91994,plain,
    ( k2_tarski(sK4,sK4) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_91565,c_39,c_40,c_41,c_1901,c_4504,c_5639,c_6429,c_90840])).

cnf(c_92855,plain,
    ( sK4 = X0
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_91994,c_1530])).

cnf(c_94385,plain,
    ( sK0(u1_struct_0(k1_tex_2(sK3,sK4))) = sK4 ),
    inference(superposition,[status(thm)],[c_87361,c_92855])).

cnf(c_1521,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6452,plain,
    ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
    | v2_struct_0(X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1521])).

cnf(c_23485,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_6452])).

cnf(c_4026,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4025])).

cnf(c_23561,plain,
    ( l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23485,c_39,c_40,c_4026])).

cnf(c_1522,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_23566,plain,
    ( l1_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23561,c_1522])).

cnf(c_1520,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8431,plain,
    ( k2_tarski(sK0(u1_struct_0(X0)),sK0(u1_struct_0(X0))) = k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X0)))
    | v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6988,c_1520])).

cnf(c_25542,plain,
    ( k2_tarski(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) = k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK0(u1_struct_0(k1_tex_2(sK3,sK4))))
    | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23566,c_8431])).

cnf(c_25921,plain,
    ( k2_tarski(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) = k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25542,c_39,c_40,c_5639])).

cnf(c_102079,plain,
    ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = k2_tarski(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_94385,c_25921])).

cnf(c_102081,plain,
    ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = u1_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_102079,c_91994])).

cnf(c_102512,plain,
    ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_102081,c_3965])).

cnf(c_102544,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_102512,c_102081])).

cnf(c_102515,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
    | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
    | v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
    | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
    | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_102081,c_1507])).

cnf(c_102094,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_94385,c_2774])).

cnf(c_92083,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_91994,c_4256])).

cnf(c_14,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1523,plain,
    ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_11,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1544,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1523,c_11])).

cnf(c_93196,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_92083,c_1544])).

cnf(c_88224,plain,
    ( ~ v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_88227,plain,
    ( v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88224])).

cnf(c_4529,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),X0)
    | X0 != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3093])).

cnf(c_9396,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(X0))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4529])).

cnf(c_88223,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
    | u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_9396])).

cnf(c_88225,plain,
    ( u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
    | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
    | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_88223])).

cnf(c_4530,plain,
    ( k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_24,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_414,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_20])).

cnf(c_415,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_414])).

cnf(c_2054,plain,
    ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
    | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_415])).

cnf(c_2058,plain,
    ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
    | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2054])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102544,c_102515,c_102094,c_93196,c_88227,c_88225,c_5639,c_4530,c_4504,c_4419,c_2058,c_1916,c_1901,c_41,c_40,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:22:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.49/3.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.49/3.50  
% 23.49/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.49/3.50  
% 23.49/3.50  ------  iProver source info
% 23.49/3.50  
% 23.49/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.49/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.49/3.50  git: non_committed_changes: false
% 23.49/3.50  git: last_make_outside_of_git: false
% 23.49/3.50  
% 23.49/3.50  ------ 
% 23.49/3.50  ------ Parsing...
% 23.49/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.49/3.50  
% 23.49/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.49/3.50  
% 23.49/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.49/3.50  
% 23.49/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.49/3.50  ------ Proving...
% 23.49/3.50  ------ Problem Properties 
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  clauses                                 38
% 23.49/3.50  conjectures                             5
% 23.49/3.50  EPR                                     10
% 23.49/3.50  Horn                                    26
% 23.49/3.50  unary                                   7
% 23.49/3.50  binary                                  9
% 23.49/3.50  lits                                    101
% 23.49/3.50  lits eq                                 9
% 23.49/3.50  fd_pure                                 0
% 23.49/3.50  fd_pseudo                               0
% 23.49/3.50  fd_cond                                 0
% 23.49/3.50  fd_pseudo_cond                          3
% 23.49/3.50  AC symbols                              0
% 23.49/3.50  
% 23.49/3.50  ------ Input Options Time Limit: Unbounded
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  ------ 
% 23.49/3.50  Current options:
% 23.49/3.50  ------ 
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  ------ Proving...
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  % SZS status Theorem for theBenchmark.p
% 23.49/3.50  
% 23.49/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.49/3.50  
% 23.49/3.50  fof(f23,conjecture,(
% 23.49/3.50    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f24,negated_conjecture,(
% 23.49/3.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 23.49/3.50    inference(negated_conjecture,[],[f23])).
% 23.49/3.50  
% 23.49/3.50  fof(f52,plain,(
% 23.49/3.50    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f24])).
% 23.49/3.50  
% 23.49/3.50  fof(f53,plain,(
% 23.49/3.50    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f52])).
% 23.49/3.50  
% 23.49/3.50  fof(f68,plain,(
% 23.49/3.50    ? [X0] : (? [X1] : (((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.49/3.50    inference(nnf_transformation,[],[f53])).
% 23.49/3.50  
% 23.49/3.50  fof(f69,plain,(
% 23.49/3.50    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f68])).
% 23.49/3.50  
% 23.49/3.50  fof(f71,plain,(
% 23.49/3.50    ( ! [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) => ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,sK4),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),sK4),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,sK4),X0)) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 23.49/3.50    introduced(choice_axiom,[])).
% 23.49/3.50  
% 23.49/3.50  fof(f70,plain,(
% 23.49/3.50    ? [X0] : (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0)) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,X1),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),X1),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,X1),sK3)) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 23.49/3.50    introduced(choice_axiom,[])).
% 23.49/3.50  
% 23.49/3.50  fof(f72,plain,(
% 23.49/3.50    ((~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & (v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 23.49/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f69,f71,f70])).
% 23.49/3.50  
% 23.49/3.50  fof(f110,plain,(
% 23.49/3.50    m1_subset_1(sK4,u1_struct_0(sK3))),
% 23.49/3.50    inference(cnf_transformation,[],[f72])).
% 23.49/3.50  
% 23.49/3.50  fof(f5,axiom,(
% 23.49/3.50    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f28,plain,(
% 23.49/3.50    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f5])).
% 23.49/3.50  
% 23.49/3.50  fof(f62,plain,(
% 23.49/3.50    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.49/3.50    inference(nnf_transformation,[],[f28])).
% 23.49/3.50  
% 23.49/3.50  fof(f81,plain,(
% 23.49/3.50    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f62])).
% 23.49/3.50  
% 23.49/3.50  fof(f108,plain,(
% 23.49/3.50    ~v2_struct_0(sK3)),
% 23.49/3.50    inference(cnf_transformation,[],[f72])).
% 23.49/3.50  
% 23.49/3.50  fof(f109,plain,(
% 23.49/3.50    l1_pre_topc(sK3)),
% 23.49/3.50    inference(cnf_transformation,[],[f72])).
% 23.49/3.50  
% 23.49/3.50  fof(f12,axiom,(
% 23.49/3.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f32,plain,(
% 23.49/3.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f12])).
% 23.49/3.50  
% 23.49/3.50  fof(f33,plain,(
% 23.49/3.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f32])).
% 23.49/3.50  
% 23.49/3.50  fof(f91,plain,(
% 23.49/3.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f33])).
% 23.49/3.50  
% 23.49/3.50  fof(f10,axiom,(
% 23.49/3.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f30,plain,(
% 23.49/3.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f10])).
% 23.49/3.50  
% 23.49/3.50  fof(f89,plain,(
% 23.49/3.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f30])).
% 23.49/3.50  
% 23.49/3.50  fof(f18,axiom,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f26,plain,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 23.49/3.50    inference(pure_predicate_removal,[],[f18])).
% 23.49/3.50  
% 23.49/3.50  fof(f42,plain,(
% 23.49/3.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f26])).
% 23.49/3.50  
% 23.49/3.50  fof(f43,plain,(
% 23.49/3.50    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f42])).
% 23.49/3.50  
% 23.49/3.50  fof(f102,plain,(
% 23.49/3.50    ( ! [X0,X1] : (m1_pre_topc(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f43])).
% 23.49/3.50  
% 23.49/3.50  fof(f16,axiom,(
% 23.49/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f39,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f16])).
% 23.49/3.50  
% 23.49/3.50  fof(f40,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(flattening,[],[f39])).
% 23.49/3.50  
% 23.49/3.50  fof(f63,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(nnf_transformation,[],[f40])).
% 23.49/3.50  
% 23.49/3.50  fof(f64,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(rectify,[],[f63])).
% 23.49/3.50  
% 23.49/3.50  fof(f65,plain,(
% 23.49/3.50    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.49/3.50    introduced(choice_axiom,[])).
% 23.49/3.50  
% 23.49/3.50  fof(f66,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK2(X0,X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f64,f65])).
% 23.49/3.50  
% 23.49/3.50  fof(f97,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f66])).
% 23.49/3.50  
% 23.49/3.50  fof(f21,axiom,(
% 23.49/3.50    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f48,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f21])).
% 23.49/3.50  
% 23.49/3.50  fof(f49,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 23.49/3.50    inference(flattening,[],[f48])).
% 23.49/3.50  
% 23.49/3.50  fof(f106,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f49])).
% 23.49/3.50  
% 23.49/3.50  fof(f4,axiom,(
% 23.49/3.50    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f27,plain,(
% 23.49/3.50    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f4])).
% 23.49/3.50  
% 23.49/3.50  fof(f80,plain,(
% 23.49/3.50    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f27])).
% 23.49/3.50  
% 23.49/3.50  fof(f112,plain,(
% 23.49/3.50    ~v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | ~v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 23.49/3.50    inference(cnf_transformation,[],[f72])).
% 23.49/3.50  
% 23.49/3.50  fof(f2,axiom,(
% 23.49/3.50    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f58,plain,(
% 23.49/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 23.49/3.50    inference(nnf_transformation,[],[f2])).
% 23.49/3.50  
% 23.49/3.50  fof(f59,plain,(
% 23.49/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.49/3.50    inference(rectify,[],[f58])).
% 23.49/3.50  
% 23.49/3.50  fof(f60,plain,(
% 23.49/3.50    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 23.49/3.50    introduced(choice_axiom,[])).
% 23.49/3.50  
% 23.49/3.50  fof(f61,plain,(
% 23.49/3.50    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 23.49/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f59,f60])).
% 23.49/3.50  
% 23.49/3.50  fof(f77,plain,(
% 23.49/3.50    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f61])).
% 23.49/3.50  
% 23.49/3.50  fof(f3,axiom,(
% 23.49/3.50    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f79,plain,(
% 23.49/3.50    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f3])).
% 23.49/3.50  
% 23.49/3.50  fof(f114,plain,(
% 23.49/3.50    ( ! [X0,X1] : (k2_tarski(X0,X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 23.49/3.50    inference(definition_unfolding,[],[f77,f79])).
% 23.49/3.50  
% 23.49/3.50  fof(f75,plain,(
% 23.49/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 23.49/3.50    inference(cnf_transformation,[],[f61])).
% 23.49/3.50  
% 23.49/3.50  fof(f116,plain,(
% 23.49/3.50    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 23.49/3.50    inference(definition_unfolding,[],[f75,f79])).
% 23.49/3.50  
% 23.49/3.50  fof(f120,plain,(
% 23.49/3.50    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 23.49/3.50    inference(equality_resolution,[],[f116])).
% 23.49/3.50  
% 23.49/3.50  fof(f14,axiom,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f36,plain,(
% 23.49/3.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f14])).
% 23.49/3.50  
% 23.49/3.50  fof(f37,plain,(
% 23.49/3.50    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 23.49/3.50    inference(flattening,[],[f36])).
% 23.49/3.50  
% 23.49/3.50  fof(f93,plain,(
% 23.49/3.50    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f37])).
% 23.49/3.50  
% 23.49/3.50  fof(f117,plain,(
% 23.49/3.50    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(definition_unfolding,[],[f93,f79])).
% 23.49/3.50  
% 23.49/3.50  fof(f13,axiom,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f34,plain,(
% 23.49/3.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f13])).
% 23.49/3.50  
% 23.49/3.50  fof(f35,plain,(
% 23.49/3.50    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 23.49/3.50    inference(flattening,[],[f34])).
% 23.49/3.50  
% 23.49/3.50  fof(f92,plain,(
% 23.49/3.50    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f35])).
% 23.49/3.50  
% 23.49/3.50  fof(f17,axiom,(
% 23.49/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f41,plain,(
% 23.49/3.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f17])).
% 23.49/3.50  
% 23.49/3.50  fof(f67,plain,(
% 23.49/3.50    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.49/3.50    inference(nnf_transformation,[],[f41])).
% 23.49/3.50  
% 23.49/3.50  fof(f100,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.49/3.50    inference(cnf_transformation,[],[f67])).
% 23.49/3.50  
% 23.49/3.50  fof(f20,axiom,(
% 23.49/3.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f46,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : ((~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0)) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f20])).
% 23.49/3.50  
% 23.49/3.50  fof(f47,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_xboole_0(X0))),
% 23.49/3.50    inference(flattening,[],[f46])).
% 23.49/3.50  
% 23.49/3.50  fof(f105,plain,(
% 23.49/3.50    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | ~v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f47])).
% 23.49/3.50  
% 23.49/3.50  fof(f111,plain,(
% 23.49/3.50    v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) | v1_tex_2(k1_tex_2(sK3,sK4),sK3)),
% 23.49/3.50    inference(cnf_transformation,[],[f72])).
% 23.49/3.50  
% 23.49/3.50  fof(f1,axiom,(
% 23.49/3.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f54,plain,(
% 23.49/3.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 23.49/3.50    inference(nnf_transformation,[],[f1])).
% 23.49/3.50  
% 23.49/3.50  fof(f55,plain,(
% 23.49/3.50    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.49/3.50    inference(rectify,[],[f54])).
% 23.49/3.50  
% 23.49/3.50  fof(f56,plain,(
% 23.49/3.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 23.49/3.50    introduced(choice_axiom,[])).
% 23.49/3.50  
% 23.49/3.50  fof(f57,plain,(
% 23.49/3.50    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 23.49/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 23.49/3.50  
% 23.49/3.50  fof(f74,plain,(
% 23.49/3.50    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f57])).
% 23.49/3.50  
% 23.49/3.50  fof(f82,plain,(
% 23.49/3.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f62])).
% 23.49/3.50  
% 23.49/3.50  fof(f73,plain,(
% 23.49/3.50    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f57])).
% 23.49/3.50  
% 23.49/3.50  fof(f96,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f66])).
% 23.49/3.50  
% 23.49/3.50  fof(f8,axiom,(
% 23.49/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f29,plain,(
% 23.49/3.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f8])).
% 23.49/3.50  
% 23.49/3.50  fof(f87,plain,(
% 23.49/3.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.49/3.50    inference(cnf_transformation,[],[f29])).
% 23.49/3.50  
% 23.49/3.50  fof(f15,axiom,(
% 23.49/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f38,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f15])).
% 23.49/3.50  
% 23.49/3.50  fof(f94,plain,(
% 23.49/3.50    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f38])).
% 23.49/3.50  
% 23.49/3.50  fof(f11,axiom,(
% 23.49/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f31,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.49/3.50    inference(ennf_transformation,[],[f11])).
% 23.49/3.50  
% 23.49/3.50  fof(f90,plain,(
% 23.49/3.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f31])).
% 23.49/3.50  
% 23.49/3.50  fof(f19,axiom,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f25,plain,(
% 23.49/3.50    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 23.49/3.50    inference(pure_predicate_removal,[],[f19])).
% 23.49/3.50  
% 23.49/3.50  fof(f44,plain,(
% 23.49/3.50    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f25])).
% 23.49/3.50  
% 23.49/3.50  fof(f45,plain,(
% 23.49/3.50    ! [X0,X1] : ((v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f44])).
% 23.49/3.50  
% 23.49/3.50  fof(f103,plain,(
% 23.49/3.50    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f45])).
% 23.49/3.50  
% 23.49/3.50  fof(f98,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f66])).
% 23.49/3.50  
% 23.49/3.50  fof(f104,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f45])).
% 23.49/3.50  
% 23.49/3.50  fof(f76,plain,(
% 23.49/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 23.49/3.50    inference(cnf_transformation,[],[f61])).
% 23.49/3.50  
% 23.49/3.50  fof(f115,plain,(
% 23.49/3.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 23.49/3.50    inference(definition_unfolding,[],[f76,f79])).
% 23.49/3.50  
% 23.49/3.50  fof(f118,plain,(
% 23.49/3.50    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 23.49/3.50    inference(equality_resolution,[],[f115])).
% 23.49/3.50  
% 23.49/3.50  fof(f119,plain,(
% 23.49/3.50    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 23.49/3.50    inference(equality_resolution,[],[f118])).
% 23.49/3.50  
% 23.49/3.50  fof(f84,plain,(
% 23.49/3.50    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f62])).
% 23.49/3.50  
% 23.49/3.50  fof(f22,axiom,(
% 23.49/3.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f50,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 23.49/3.50    inference(ennf_transformation,[],[f22])).
% 23.49/3.50  
% 23.49/3.50  fof(f51,plain,(
% 23.49/3.50    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 23.49/3.50    inference(flattening,[],[f50])).
% 23.49/3.50  
% 23.49/3.50  fof(f107,plain,(
% 23.49/3.50    ( ! [X0,X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f51])).
% 23.49/3.50  
% 23.49/3.50  fof(f9,axiom,(
% 23.49/3.50    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f88,plain,(
% 23.49/3.50    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f9])).
% 23.49/3.50  
% 23.49/3.50  fof(f6,axiom,(
% 23.49/3.50    ! [X0] : k2_subset_1(X0) = X0),
% 23.49/3.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.49/3.50  
% 23.49/3.50  fof(f85,plain,(
% 23.49/3.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 23.49/3.50    inference(cnf_transformation,[],[f6])).
% 23.49/3.50  
% 23.49/3.50  fof(f95,plain,(
% 23.49/3.50    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(cnf_transformation,[],[f66])).
% 23.49/3.50  
% 23.49/3.50  fof(f121,plain,(
% 23.49/3.50    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.49/3.50    inference(equality_resolution,[],[f95])).
% 23.49/3.50  
% 23.49/3.50  cnf(c_36,negated_conjecture,
% 23.49/3.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 23.49/3.50      inference(cnf_transformation,[],[f110]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1504,plain,
% 23.49/3.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_10,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1526,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) != iProver_top
% 23.49/3.50      | r2_hidden(X0,X1) = iProver_top
% 23.49/3.50      | v1_xboole_0(X1) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2940,plain,
% 23.49/3.50      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1504,c_1526]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_38,negated_conjecture,
% 23.49/3.50      ( ~ v2_struct_0(sK3) ),
% 23.49/3.50      inference(cnf_transformation,[],[f108]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_39,plain,
% 23.49/3.50      ( v2_struct_0(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_37,negated_conjecture,
% 23.49/3.50      ( l1_pre_topc(sK3) ),
% 23.49/3.50      inference(cnf_transformation,[],[f109]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_40,plain,
% 23.49/3.50      ( l1_pre_topc(sK3) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_17,plain,
% 23.49/3.50      ( v2_struct_0(X0)
% 23.49/3.50      | ~ l1_struct_0(X0)
% 23.49/3.50      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 23.49/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_90,plain,
% 23.49/3.50      ( v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_92,plain,
% 23.49/3.50      ( v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_struct_0(sK3) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_90]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_15,plain,
% 23.49/3.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_94,plain,
% 23.49/3.50      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_96,plain,
% 23.49/3.50      ( l1_pre_topc(sK3) != iProver_top
% 23.49/3.50      | l1_struct_0(sK3) = iProver_top ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_94]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1980,plain,
% 23.49/3.50      ( r2_hidden(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) ),
% 23.49/3.50      inference(resolution,[status(thm)],[c_10,c_36]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1981,plain,
% 23.49/3.50      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_1980]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3061,plain,
% 23.49/3.50      ( r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_2940,c_39,c_40,c_92,c_96,c_1981]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_27,plain,
% 23.49/3.50      ( m1_pre_topc(k1_tex_2(X0,X1),X0)
% 23.49/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.49/3.50      | v2_struct_0(X0)
% 23.49/3.50      | ~ l1_pre_topc(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1511,plain,
% 23.49/3.50      ( m1_pre_topc(k1_tex_2(X0,X1),X0) = iProver_top
% 23.49/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_22,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1)
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | ~ l1_pre_topc(X1)
% 23.49/3.50      | sK2(X1,X0) = u1_struct_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f97]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1515,plain,
% 23.49/3.50      ( sK2(X0,X1) = u1_struct_0(X1)
% 23.49/3.50      | v1_tex_2(X1,X0) = iProver_top
% 23.49/3.50      | m1_pre_topc(X1,X0) != iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6453,plain,
% 23.49/3.50      ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(k1_tex_2(X0,X1))
% 23.49/3.50      | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
% 23.49/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1511,c_1515]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_32,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 23.49/3.50      | ~ m1_subset_1(X1,X0)
% 23.49/3.50      | v1_zfmisc_1(X0)
% 23.49/3.50      | v1_xboole_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f106]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6,plain,
% 23.49/3.50      ( v1_zfmisc_1(X0) | ~ v1_xboole_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_379,plain,
% 23.49/3.50      ( v1_zfmisc_1(X0)
% 23.49/3.50      | ~ m1_subset_1(X1,X0)
% 23.49/3.50      | v1_subset_1(k6_domain_1(X0,X1),X0) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_32,c_6]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_380,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(X0,X1),X0)
% 23.49/3.50      | ~ m1_subset_1(X1,X0)
% 23.49/3.50      | v1_zfmisc_1(X0) ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_379]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1500,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 23.49/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_34,negated_conjecture,
% 23.49/3.50      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
% 23.49/3.50      inference(cnf_transformation,[],[f112]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1506,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2615,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1500,c_1506]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_41,plain,
% 23.49/3.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3054,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_2615,c_41]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_36181,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_6453,c_3054]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_38133,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_36181,c_39,c_40,c_41]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3,plain,
% 23.49/3.50      ( r2_hidden(sK1(X0,X1),X1)
% 23.49/3.50      | sK1(X0,X1) = X0
% 23.49/3.50      | k2_tarski(X0,X0) = X1 ),
% 23.49/3.50      inference(cnf_transformation,[],[f114]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1532,plain,
% 23.49/3.50      ( sK1(X0,X1) = X0
% 23.49/3.50      | k2_tarski(X0,X0) = X1
% 23.49/3.50      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5,plain,
% 23.49/3.50      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 23.49/3.50      inference(cnf_transformation,[],[f120]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1530,plain,
% 23.49/3.50      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3933,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(X1,X1)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(X1,X1)) = X1
% 23.49/3.50      | k2_tarski(X1,X1) = k2_tarski(X0,X0) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1532,c_1530]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_19,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,X1)
% 23.49/3.50      | v1_xboole_0(X1)
% 23.49/3.50      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f117]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1518,plain,
% 23.49/3.50      ( k6_domain_1(X0,X1) = k2_tarski(X1,X1)
% 23.49/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3753,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4)
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1504,c_1518]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_91,plain,
% 23.49/3.50      ( v2_struct_0(sK3)
% 23.49/3.50      | ~ l1_struct_0(sK3)
% 23.49/3.50      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_95,plain,
% 23.49/3.50      ( ~ l1_pre_topc(sK3) | l1_struct_0(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_15]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1908,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X1))
% 23.49/3.50      | k6_domain_1(u1_struct_0(X1),X0) = k2_tarski(X0,X0) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_19]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2184,plain,
% 23.49/3.50      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3))
% 23.49/3.50      | k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_1908]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4253,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(sK3),sK4) = k2_tarski(sK4,sK4) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_3753,c_38,c_37,c_36,c_91,c_95,c_2184]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_18,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,X1)
% 23.49/3.50      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 23.49/3.50      | v1_xboole_0(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f92]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1519,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) != iProver_top
% 23.49/3.50      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 23.49/3.50      | v1_xboole_0(X1) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4268,plain,
% 23.49/3.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_4253,c_1519]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5067,plain,
% 23.49/3.50      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_4268,c_39,c_40,c_41,c_92,c_96]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_16893,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3933,c_5067]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_25,plain,
% 23.49/3.50      ( v1_subset_1(X0,X1)
% 23.49/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.49/3.50      | X0 = X1 ),
% 23.49/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1513,plain,
% 23.49/3.50      ( X0 = X1
% 23.49/3.50      | v1_subset_1(X0,X1) = iProver_top
% 23.49/3.50      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_18875,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | k2_tarski(X0,X0) = u1_struct_0(sK3)
% 23.49/3.50      | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_16893,c_1513]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_31,plain,
% 23.49/3.50      ( ~ v1_subset_1(k6_domain_1(X0,X1),X0)
% 23.49/3.50      | ~ m1_subset_1(X1,X0)
% 23.49/3.50      | ~ v1_zfmisc_1(X0)
% 23.49/3.50      | v1_xboole_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f105]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1508,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(X0,X1),X0) != iProver_top
% 23.49/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5110,plain,
% 23.49/3.50      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_4253,c_1508]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6057,plain,
% 23.49/3.50      ( v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_5110,c_39,c_40,c_41,c_92,c_96]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6058,plain,
% 23.49/3.50      ( v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_6057]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_16892,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3933,c_6058]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_33450,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | k2_tarski(X0,X0) = u1_struct_0(sK3)
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_18875,c_16892]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_38140,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | k2_tarski(X0,X0) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_38133,c_33450]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_35,negated_conjecture,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) ),
% 23.49/3.50      inference(cnf_transformation,[],[f111]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1505,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK4),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4256,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(demodulation,[status(thm)],[c_4253,c_1505]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_38979,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | sK1(sK4,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_38140,c_4256]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1915,plain,
% 23.49/3.50      ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 23.49/3.50      | v2_struct_0(sK3)
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_27]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1916,plain,
% 23.49/3.50      ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_1915]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2053,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ l1_pre_topc(sK3)
% 23.49/3.50      | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_22]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2060,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_2053]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_40370,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_38979,c_39,c_40,c_41,c_1916,c_2060]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_40371,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_40370]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3965,plain,
% 23.49/3.50      ( k6_domain_1(X0,X1) = X0
% 23.49/3.50      | v1_subset_1(k6_domain_1(X0,X1),X0) = iProver_top
% 23.49/3.50      | m1_subset_1(X1,X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1519,c_1513]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_0,plain,
% 23.49/3.50      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1535,plain,
% 23.49/3.50      ( r2_hidden(sK0(X0),X0) = iProver_top
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1,plain,
% 23.49/3.50      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f73]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_356,plain,
% 23.49/3.50      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 23.49/3.50      inference(global_propositional_subsumption,[status(thm)],[c_9,c_1]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_357,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_356]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1501,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.49/3.50      | r2_hidden(X0,X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2774,plain,
% 23.49/3.50      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1535,c_1501]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6988,plain,
% 23.49/3.50      ( k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
% 23.49/3.50      | v1_xboole_0(X0) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_2774,c_1518]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1534,plain,
% 23.49/3.50      ( r2_hidden(X0,X1) != iProver_top
% 23.49/3.50      | v1_xboole_0(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3066,plain,
% 23.49/3.50      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3061,c_1534]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_8432,plain,
% 23.49/3.50      ( k2_tarski(sK0(u1_struct_0(sK3)),sK0(u1_struct_0(sK3))) = k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_6988,c_3066]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4257,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(demodulation,[status(thm)],[c_4253,c_1506]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_16897,plain,
% 23.49/3.50      ( sK1(X0,k2_tarski(sK4,sK4)) = X0
% 23.49/3.50      | sK1(X0,k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(k2_tarski(X0,X0),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3933,c_4257]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_18603,plain,
% 23.49/3.50      ( sK1(sK0(u1_struct_0(sK3)),k2_tarski(sK4,sK4)) = sK0(u1_struct_0(sK3))
% 23.49/3.50      | sK1(sK0(u1_struct_0(sK3)),k2_tarski(sK4,sK4)) = sK4
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_8432,c_16897]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1995,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0))
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1996,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1998,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_1996]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1890,plain,
% 23.49/3.50      ( m1_subset_1(X0,u1_struct_0(X1))
% 23.49/3.50      | ~ r2_hidden(X0,u1_struct_0(X1)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_357]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2122,plain,
% 23.49/3.50      ( m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X0))
% 23.49/3.50      | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_1890]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2123,plain,
% 23.49/3.50      ( m1_subset_1(sK0(u1_struct_0(X0)),u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_2122]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2125,plain,
% 23.49/3.50      ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_2123]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5810,plain,
% 23.49/3.50      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3))
% 23.49/3.50      | ~ m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
% 23.49/3.50      | ~ v1_zfmisc_1(u1_struct_0(sK3))
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_31]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5811,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_5810]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_21984,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_18603,c_39,c_40,c_41,c_92,c_96,c_1998,c_2125,c_2615,
% 23.49/3.50                 c_5811]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_21990,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3965,c_21984]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_44328,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3)
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_21990,c_39,c_40,c_92,c_96,c_1998,c_2125]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_44334,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_40371,c_44328]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_8482,plain,
% 23.49/3.50      ( sK0(u1_struct_0(sK3)) = X0
% 23.49/3.50      | r2_hidden(X0,k6_domain_1(u1_struct_0(sK3),sK0(u1_struct_0(sK3)))) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_8432,c_1530]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_44694,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | sK0(u1_struct_0(sK3)) = X0
% 23.49/3.50      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_44334,c_8482]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_45029,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | sK0(u1_struct_0(sK3)) = sK4 ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_3061,c_44694]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_23,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1)
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1514,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1) = iProver_top
% 23.49/3.50      | m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_13,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.49/3.50      | ~ r2_hidden(X2,X0)
% 23.49/3.50      | r2_hidden(X2,X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f87]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1524,plain,
% 23.49/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.49/3.50      | r2_hidden(X2,X0) != iProver_top
% 23.49/3.50      | r2_hidden(X2,X1) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6643,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1) = iProver_top
% 23.49/3.50      | m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | r2_hidden(X2,sK2(X1,X0)) != iProver_top
% 23.49/3.50      | r2_hidden(X2,u1_struct_0(X1)) = iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1514,c_1524]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_45154,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1) = iProver_top
% 23.49/3.50      | m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | r2_hidden(sK0(sK2(X1,X0)),u1_struct_0(X1)) = iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top
% 23.49/3.50      | v1_xboole_0(sK2(X1,X0)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1535,c_6643]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_86279,plain,
% 23.49/3.50      ( sK0(u1_struct_0(sK3)) = sK4
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top
% 23.49/3.50      | v1_xboole_0(sK2(sK3,k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_45029,c_45154]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_20,plain,
% 23.49/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2055,plain,
% 23.49/3.50      ( ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_20]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2056,plain,
% 23.49/3.50      ( m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_2055]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2041,plain,
% 23.49/3.50      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(X1))
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(X0)),X1)
% 23.49/3.50      | ~ r2_hidden(sK0(u1_struct_0(X0)),u1_struct_0(X0)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_13]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2598,plain,
% 23.49/3.50      ( ~ m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3)))
% 23.49/3.50      | ~ r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_2041]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2599,plain,
% 23.49/3.50      ( m1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
% 23.49/3.50      | r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_2598]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3050,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_1995]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3051,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_3050]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4418,plain,
% 23.49/3.50      ( v2_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | ~ l1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | ~ v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_17]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4419,plain,
% 23.49/3.50      ( v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_4418]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_16,plain,
% 23.49/3.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3791,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.49/3.50      | v2_struct_0(X1)
% 23.49/3.50      | ~ l1_pre_topc(X1)
% 23.49/3.50      | l1_pre_topc(k1_tex_2(X1,X0)) ),
% 23.49/3.50      inference(resolution,[status(thm)],[c_16,c_27]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4025,plain,
% 23.49/3.50      ( v2_struct_0(sK3)
% 23.49/3.50      | l1_pre_topc(k1_tex_2(sK3,sK4))
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(resolution,[status(thm)],[c_3791,c_36]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4491,plain,
% 23.49/3.50      ( l1_pre_topc(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_4025,c_38,c_37]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4503,plain,
% 23.49/3.50      ( l1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(resolution,[status(thm)],[c_4491,c_15]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4504,plain,
% 23.49/3.50      ( l1_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_4503]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_30,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.49/3.50      | v2_struct_0(X1)
% 23.49/3.50      | ~ v2_struct_0(k1_tex_2(X1,X0))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f103]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1510,plain,
% 23.49/3.50      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 23.49/3.50      | v2_struct_0(X1) = iProver_top
% 23.49/3.50      | v2_struct_0(k1_tex_2(X1,X0)) != iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5639,plain,
% 23.49/3.50      ( v2_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 23.49/3.50      | v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1504,c_1510]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_87361,plain,
% 23.49/3.50      ( r2_hidden(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_86279,c_39,c_40,c_41,c_1916,c_2056,c_2599,c_3051,
% 23.49/3.50                 c_4419,c_4504,c_5639]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6644,plain,
% 23.49/3.50      ( sK2(X0,X1) = u1_struct_0(X0)
% 23.49/3.50      | v1_tex_2(X1,X0) = iProver_top
% 23.49/3.50      | m1_pre_topc(X1,X0) != iProver_top
% 23.49/3.50      | v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1514,c_1513]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_21,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1)
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | ~ v1_subset_1(sK2(X1,X0),u1_struct_0(X1))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f98]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1516,plain,
% 23.49/3.50      ( v1_tex_2(X0,X1) = iProver_top
% 23.49/3.50      | m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | v1_subset_1(sK2(X1,X0),u1_struct_0(X1)) != iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_49175,plain,
% 23.49/3.50      ( sK2(X0,X1) = u1_struct_0(X0)
% 23.49/3.50      | v1_tex_2(X1,X0) = iProver_top
% 23.49/3.50      | m1_pre_topc(X1,X0) != iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(forward_subsumption_resolution,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_6644,c_1516]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_49177,plain,
% 23.49/3.50      ( sK2(X0,k1_tex_2(X0,X1)) = u1_struct_0(X0)
% 23.49/3.50      | v1_tex_2(k1_tex_2(X0,X1),X0) = iProver_top
% 23.49/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1511,c_49175]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_91487,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_49177,c_3054]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_91556,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_91487,c_39,c_40,c_41]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_5075,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
% 23.49/3.50      | v1_subset_1(k2_tarski(sK4,sK4),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_5067,c_1513]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6429,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_5075,c_6058]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_91565,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | k2_tarski(sK4,sK4) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_91556,c_6429]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_29,plain,
% 23.49/3.50      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 23.49/3.50      | v7_struct_0(k1_tex_2(X1,X0))
% 23.49/3.50      | v2_struct_0(X1)
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f104]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1900,plain,
% 23.49/3.50      ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
% 23.49/3.50      | v7_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v2_struct_0(sK3)
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_29]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1901,plain,
% 23.49/3.50      ( m1_subset_1(sK4,u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v7_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1517,plain,
% 23.49/3.50      ( m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4201,plain,
% 23.49/3.50      ( u1_struct_0(X0) = u1_struct_0(X1)
% 23.49/3.50      | m1_pre_topc(X1,X0) != iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | l1_pre_topc(X0) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1517,c_1513]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47276,plain,
% 23.49/3.50      ( sK0(u1_struct_0(sK3)) = sK4
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_45029,c_1516]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_119,plain,
% 23.49/3.50      ( ~ r2_hidden(sK3,k2_tarski(sK3,sK3)) | sK3 = sK3 ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_5]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4,plain,
% 23.49/3.50      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 23.49/3.50      inference(cnf_transformation,[],[f119]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_122,plain,
% 23.49/3.50      ( r2_hidden(sK3,k2_tarski(sK3,sK3)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_4]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_690,plain,
% 23.49/3.50      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.49/3.50      theory(equality) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_703,plain,
% 23.49/3.50      ( u1_struct_0(sK3) = u1_struct_0(sK3) | sK3 != sK3 ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_690]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_687,plain,
% 23.49/3.50      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.49/3.50      theory(equality) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3093,plain,
% 23.49/3.50      ( v1_subset_1(X0,X1)
% 23.49/3.50      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | X0 != u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | X1 != u1_struct_0(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_687]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4546,plain,
% 23.49/3.50      ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),X0)
% 23.49/3.50      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | X0 != u1_struct_0(sK3)
% 23.49/3.50      | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_3093]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6967,plain,
% 23.49/3.50      ( v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(X0))
% 23.49/3.50      | ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | u1_struct_0(X0) != u1_struct_0(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_4546]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6968,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.49/3.50      | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_6967]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6970,plain,
% 23.49/3.50      ( sK2(sK3,k1_tex_2(sK3,sK4)) != u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | u1_struct_0(sK3) != u1_struct_0(sK3)
% 23.49/3.50      | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_6968]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_10967,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_21]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_10968,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(sK2(sK3,k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_10967]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47307,plain,
% 23.49/3.50      ( v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_47276,c_39,c_40,c_41,c_119,c_122,c_703,c_1916,c_2060,
% 23.49/3.50                 c_6970,c_10968]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47308,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_47307]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47314,plain,
% 23.49/3.50      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_4201,c_47308]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47963,plain,
% 23.49/3.50      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_47314,c_39,c_40,c_41,c_1916]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6431,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
% 23.49/3.50      | v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_5075,c_4257]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_47972,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
% 23.49/3.50      | u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_47963,c_6431]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_7,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | ~ v1_xboole_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1528,plain,
% 23.49/3.50      ( m1_subset_1(X0,X1) = iProver_top
% 23.49/3.50      | v1_xboole_0(X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(X1) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_33,plain,
% 23.49/3.50      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
% 23.49/3.50      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 23.49/3.50      | ~ v7_struct_0(X0)
% 23.49/3.50      | v2_struct_0(X0)
% 23.49/3.50      | ~ l1_struct_0(X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f107]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1507,plain,
% 23.49/3.50      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) != iProver_top
% 23.49/3.50      | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
% 23.49/3.50      | v7_struct_0(X0) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_3721,plain,
% 23.49/3.50      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 23.49/3.50      | v7_struct_0(X1) != iProver_top
% 23.49/3.50      | v2_struct_0(X1) = iProver_top
% 23.49/3.50      | l1_struct_0(X1) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(X1)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1500,c_1507]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9155,plain,
% 23.49/3.50      ( v7_struct_0(X0) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | v1_xboole_0(X1) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1528,c_3721]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9157,plain,
% 23.49/3.50      ( v7_struct_0(X0) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_2774,c_3721]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9178,plain,
% 23.49/3.50      ( v7_struct_0(X0) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top
% 23.49/3.50      | v1_xboole_0(X1) != iProver_top ),
% 23.49/3.50      inference(forward_subsumption_resolution,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_9155,c_9157]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9184,plain,
% 23.49/3.50      ( v7_struct_0(X0) != iProver_top
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(X0)) = iProver_top ),
% 23.49/3.50      inference(backward_subsumption_resolution,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_9178,c_9157]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_90840,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3)
% 23.49/3.50      | v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 23.49/3.50      | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 23.49/3.50      | v1_zfmisc_1(u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_47972,c_9184]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_91994,plain,
% 23.49/3.50      ( k2_tarski(sK4,sK4) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_91565,c_39,c_40,c_41,c_1901,c_4504,c_5639,c_6429,
% 23.49/3.50                 c_90840]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_92855,plain,
% 23.49/3.50      ( sK4 = X0 | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_91994,c_1530]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_94385,plain,
% 23.49/3.50      ( sK0(u1_struct_0(k1_tex_2(sK3,sK4))) = sK4 ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_87361,c_92855]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1521,plain,
% 23.49/3.50      ( m1_pre_topc(X0,X1) != iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top
% 23.49/3.50      | l1_pre_topc(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_6452,plain,
% 23.49/3.50      ( m1_subset_1(X0,u1_struct_0(X1)) != iProver_top
% 23.49/3.50      | v2_struct_0(X1) = iProver_top
% 23.49/3.50      | l1_pre_topc(X1) != iProver_top
% 23.49/3.50      | l1_pre_topc(k1_tex_2(X1,X0)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1511,c_1521]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_23485,plain,
% 23.49/3.50      ( v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_1504,c_6452]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4026,plain,
% 23.49/3.50      ( v2_struct_0(sK3) = iProver_top
% 23.49/3.50      | l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_4025]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_23561,plain,
% 23.49/3.50      ( l1_pre_topc(k1_tex_2(sK3,sK4)) = iProver_top ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_23485,c_39,c_40,c_4026]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1522,plain,
% 23.49/3.50      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_23566,plain,
% 23.49/3.50      ( l1_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_23561,c_1522]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1520,plain,
% 23.49/3.50      ( v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(X0)) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_8431,plain,
% 23.49/3.50      ( k2_tarski(sK0(u1_struct_0(X0)),sK0(u1_struct_0(X0))) = k6_domain_1(u1_struct_0(X0),sK0(u1_struct_0(X0)))
% 23.49/3.50      | v2_struct_0(X0) = iProver_top
% 23.49/3.50      | l1_struct_0(X0) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_6988,c_1520]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_25542,plain,
% 23.49/3.50      ( k2_tarski(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) = k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK0(u1_struct_0(k1_tex_2(sK3,sK4))))
% 23.49/3.50      | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_23566,c_8431]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_25921,plain,
% 23.49/3.50      ( k2_tarski(sK0(u1_struct_0(k1_tex_2(sK3,sK4))),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) = k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK0(u1_struct_0(k1_tex_2(sK3,sK4)))) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_25542,c_39,c_40,c_5639]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102079,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = k2_tarski(sK4,sK4) ),
% 23.49/3.50      inference(demodulation,[status(thm)],[c_94385,c_25921]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102081,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = u1_struct_0(sK3) ),
% 23.49/3.50      inference(light_normalisation,[status(thm)],[c_102079,c_91994]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102512,plain,
% 23.49/3.50      ( k6_domain_1(u1_struct_0(k1_tex_2(sK3,sK4)),sK4) = u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_102081,c_3965]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102544,plain,
% 23.49/3.50      ( u1_struct_0(k1_tex_2(sK3,sK4)) = u1_struct_0(sK3)
% 23.49/3.50      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(light_normalisation,[status(thm)],[c_102512,c_102081]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102515,plain,
% 23.49/3.50      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
% 23.49/3.50      | m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top
% 23.49/3.50      | v7_struct_0(k1_tex_2(sK3,sK4)) != iProver_top
% 23.49/3.50      | v2_struct_0(k1_tex_2(sK3,sK4)) = iProver_top
% 23.49/3.50      | l1_struct_0(k1_tex_2(sK3,sK4)) != iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_102081,c_1507]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_102094,plain,
% 23.49/3.50      ( m1_subset_1(sK4,u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top
% 23.49/3.50      | v1_xboole_0(u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(superposition,[status(thm)],[c_94385,c_2774]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_92083,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)) = iProver_top ),
% 23.49/3.50      inference(demodulation,[status(thm)],[c_91994,c_4256]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_14,plain,
% 23.49/3.50      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 23.49/3.50      inference(cnf_transformation,[],[f88]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1523,plain,
% 23.49/3.50      ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_11,plain,
% 23.49/3.50      ( k2_subset_1(X0) = X0 ),
% 23.49/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_1544,plain,
% 23.49/3.50      ( v1_subset_1(X0,X0) != iProver_top ),
% 23.49/3.50      inference(light_normalisation,[status(thm)],[c_1523,c_11]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_93196,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) = iProver_top ),
% 23.49/3.50      inference(forward_subsumption_resolution,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_92083,c_1544]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_88224,plain,
% 23.49/3.50      ( ~ v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_14]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_88227,plain,
% 23.49/3.50      ( v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_88224]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4529,plain,
% 23.49/3.50      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),X0)
% 23.49/3.50      | X0 != u1_struct_0(sK3)
% 23.49/3.50      | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_3093]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_9396,plain,
% 23.49/3.50      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(X0))
% 23.49/3.50      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.49/3.50      | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_4529]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_88223,plain,
% 23.49/3.50      ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4)))
% 23.49/3.50      | u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
% 23.49/3.50      | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_9396]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_88225,plain,
% 23.49/3.50      ( u1_struct_0(k1_tex_2(sK3,sK4)) != u1_struct_0(sK3)
% 23.49/3.50      | k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) != u1_struct_0(k1_tex_2(sK3,sK4))
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) != iProver_top
% 23.49/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))),u1_struct_0(k1_tex_2(sK3,sK4))) = iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_88223]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_4530,plain,
% 23.49/3.50      ( k2_subset_1(u1_struct_0(k1_tex_2(sK3,sK4))) = u1_struct_0(k1_tex_2(sK3,sK4)) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_11]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_24,plain,
% 23.49/3.50      ( ~ v1_tex_2(X0,X1)
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.49/3.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(cnf_transformation,[],[f121]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_414,plain,
% 23.49/3.50      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | ~ v1_tex_2(X0,X1)
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(global_propositional_subsumption,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_24,c_20]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_415,plain,
% 23.49/3.50      ( ~ v1_tex_2(X0,X1)
% 23.49/3.50      | ~ m1_pre_topc(X0,X1)
% 23.49/3.50      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.49/3.50      | ~ l1_pre_topc(X1) ),
% 23.49/3.50      inference(renaming,[status(thm)],[c_414]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2054,plain,
% 23.49/3.50      ( ~ v1_tex_2(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | ~ m1_pre_topc(k1_tex_2(sK3,sK4),sK3)
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3))
% 23.49/3.50      | ~ l1_pre_topc(sK3) ),
% 23.49/3.50      inference(instantiation,[status(thm)],[c_415]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(c_2058,plain,
% 23.49/3.50      ( v1_tex_2(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | m1_pre_topc(k1_tex_2(sK3,sK4),sK3) != iProver_top
% 23.49/3.50      | v1_subset_1(u1_struct_0(k1_tex_2(sK3,sK4)),u1_struct_0(sK3)) = iProver_top
% 23.49/3.50      | l1_pre_topc(sK3) != iProver_top ),
% 23.49/3.50      inference(predicate_to_equality,[status(thm)],[c_2054]) ).
% 23.49/3.50  
% 23.49/3.50  cnf(contradiction,plain,
% 23.49/3.50      ( $false ),
% 23.49/3.50      inference(minisat,
% 23.49/3.50                [status(thm)],
% 23.49/3.50                [c_102544,c_102515,c_102094,c_93196,c_88227,c_88225,
% 23.49/3.50                 c_5639,c_4530,c_4504,c_4419,c_2058,c_1916,c_1901,c_41,
% 23.49/3.50                 c_40,c_39]) ).
% 23.49/3.50  
% 23.49/3.50  
% 23.49/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.49/3.50  
% 23.49/3.50  ------                               Statistics
% 23.49/3.50  
% 23.49/3.50  ------ Selected
% 23.49/3.50  
% 23.49/3.50  total_time:                             2.718
% 23.49/3.50  
%------------------------------------------------------------------------------
