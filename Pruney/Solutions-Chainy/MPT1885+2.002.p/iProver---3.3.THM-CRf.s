%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:28 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 531 expanded)
%              Number of clauses        :   97 ( 197 expanded)
%              Number of leaves         :   15 ( 111 expanded)
%              Depth                    :   21
%              Number of atoms          :  533 (3256 expanded)
%              Number of equality atoms :  199 ( 529 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => ~ ( u1_struct_0(X2) = X1
                      & v4_tex_2(X2,X0) ) )
              & v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ~ ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_pre_topc(X2)
                      & ~ v2_struct_0(X2) )
                   => ~ ( u1_struct_0(X2) = X1
                        & v4_tex_2(X2,X0) ) )
                & v3_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,X0)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
     => ( ! [X2] :
            ( u1_struct_0(X2) != sK2
            | ~ v4_tex_2(X2,X0)
            | ~ m1_pre_topc(X2,X0)
            | ~ v1_pre_topc(X2)
            | v2_struct_0(X2) )
        & v3_tex_2(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( u1_struct_0(X2) != X1
                | ~ v4_tex_2(X2,X0)
                | ~ m1_pre_topc(X2,X0)
                | ~ v1_pre_topc(X2)
                | v2_struct_0(X2) )
            & v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( u1_struct_0(X2) != X1
              | ~ v4_tex_2(X2,sK1)
              | ~ m1_pre_topc(X2,sK1)
              | ~ v1_pre_topc(X2)
              | v2_struct_0(X2) )
          & v3_tex_2(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X2] :
        ( u1_struct_0(X2) != sK2
        | ~ v4_tex_2(X2,sK1)
        | ~ m1_pre_topc(X2,sK1)
        | ~ v1_pre_topc(X2)
        | v2_struct_0(X2) )
    & v3_tex_2(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & ~ v1_xboole_0(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f30,f29])).

fof(f46,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f45,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2] :
      ( u1_struct_0(X2) != sK2
      | ~ v4_tex_2(X2,sK1)
      | ~ m1_pre_topc(X2,sK1)
      | ~ v1_pre_topc(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_tex_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tex_2(X1,X0)
          <=> ! [X2] :
                ( v3_tex_2(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_tex_2(X2,X0)
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_tex_2(X2,X0)
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_tex_2(X2,X0)
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK0(X0,X1),X0)
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tex_2(X1,X0)
              | ( ~ v3_tex_2(sK0(X0,X1),X0)
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_tex_2(X3,X0)
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v4_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(sK0(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_7,plain,
    ( ~ v2_struct_0(X0)
    | v1_xboole_0(k2_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_15,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_207,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | k2_struct_0(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_223,plain,
    ( ~ v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | k2_struct_0(X0) != sK2 ),
    inference(resolution,[status(thm)],[c_5,c_207])).

cnf(c_2367,plain,
    ( ~ v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44)
    | k2_struct_0(X0_44) != sK2 ),
    inference(subtyping,[status(esa)],[c_223])).

cnf(c_4463,plain,
    ( ~ v2_struct_0(k1_pre_topc(X0_44,X0_45))
    | ~ l1_pre_topc(k1_pre_topc(X0_44,X0_45))
    | k2_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2367])).

cnf(c_4465,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
    | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_4463])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2370,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_2756,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2370])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_235,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_5,c_2])).

cnf(c_2366,plain,
    ( ~ l1_pre_topc(X0_44)
    | u1_struct_0(X0_44) = k2_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_2760,plain,
    ( u1_struct_0(X0_44) = k2_struct_0(X0_44)
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2366])).

cnf(c_3004,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2756,c_2760])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2371,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_2755,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2371])).

cnf(c_3006,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3004,c_2755])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2380,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_2746,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_3150,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3004,c_2746])).

cnf(c_19,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3308,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3150,c_19])).

cnf(c_3309,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3308])).

cnf(c_3316,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3006,c_3309])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2378,plain,
    ( ~ m1_pre_topc(X0_44,X1_44)
    | ~ l1_pre_topc(X1_44)
    | l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2748,plain,
    ( m1_pre_topc(X0_44,X1_44) != iProver_top
    | l1_pre_topc(X1_44) != iProver_top
    | l1_pre_topc(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2378])).

cnf(c_3347,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_2748])).

cnf(c_21,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2417,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2380])).

cnf(c_2419,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_3113,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),X1_44)
    | ~ l1_pre_topc(X1_44)
    | l1_pre_topc(k1_pre_topc(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_2378])).

cnf(c_3114,plain,
    ( m1_pre_topc(k1_pre_topc(X0_44,X0_45),X1_44) != iProver_top
    | l1_pre_topc(X1_44) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0_44,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3113])).

cnf(c_3116,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3114])).

cnf(c_3432,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3347,c_19,c_21,c_2419,c_3116])).

cnf(c_3437,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_3432,c_2760])).

cnf(c_12,negated_conjecture,
    ( ~ v4_tex_2(X0,sK1)
    | ~ m1_pre_topc(X0,sK1)
    | v2_struct_0(X0)
    | ~ v1_pre_topc(X0)
    | u1_struct_0(X0) != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2373,negated_conjecture,
    ( ~ v4_tex_2(X0_44,sK1)
    | ~ m1_pre_topc(X0_44,sK1)
    | v2_struct_0(X0_44)
    | ~ v1_pre_topc(X0_44)
    | u1_struct_0(X0_44) != sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_2753,plain,
    ( u1_struct_0(X0_44) != sK2
    | v4_tex_2(X0_44,sK1) != iProver_top
    | m1_pre_topc(X0_44,sK1) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | v1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2373])).

cnf(c_4127,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top
    | v1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3437,c_2753])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_13,negated_conjecture,
    ( v3_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,plain,
    ( v3_tex_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2383,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_2411,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_2384,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_2412,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_2418,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2380])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2379,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2420,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
    | l1_pre_topc(X0_44) != iProver_top
    | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2379])).

cnf(c_2422,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2420])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_111,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1,c_4,c_3])).

cnf(c_112,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_111])).

cnf(c_2368,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
    | ~ l1_pre_topc(X0_44)
    | k2_struct_0(k1_pre_topc(X0_44,X0_45)) = X0_45 ),
    inference(subtyping,[status(esa)],[c_112])).

cnf(c_2438,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_2909,plain,
    ( ~ v4_tex_2(k1_pre_topc(X0_44,X0_45),sK1)
    | ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),sK1)
    | v2_struct_0(k1_pre_topc(X0_44,X0_45))
    | ~ v1_pre_topc(k1_pre_topc(X0_44,X0_45))
    | u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_2910,plain,
    ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2
    | v4_tex_2(k1_pre_topc(X0_44,X0_45),sK1) != iProver_top
    | m1_pre_topc(k1_pre_topc(X0_44,X0_45),sK1) != iProver_top
    | v2_struct_0(k1_pre_topc(X0_44,X0_45)) = iProver_top
    | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_2912,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top
    | v1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2910])).

cnf(c_8,plain,
    ( ~ v3_tex_2(sK0(X0,X1),X0)
    | v4_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2377,plain,
    ( ~ v3_tex_2(sK0(X0_44,X1_44),X0_44)
    | v4_tex_2(X1_44,X0_44)
    | ~ m1_pre_topc(X1_44,X0_44)
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_2942,plain,
    ( ~ v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44)
    | v4_tex_2(k1_pre_topc(X0_44,X0_45),X0_44)
    | ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44)
    | v2_struct_0(X0_44)
    | ~ l1_pre_topc(X0_44) ),
    inference(instantiation,[status(thm)],[c_2377])).

cnf(c_2943,plain,
    ( v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44) != iProver_top
    | v4_tex_2(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
    | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2942])).

cnf(c_2945,plain,
    ( v3_tex_2(sK0(sK1,k1_pre_topc(sK1,sK2)),sK1) != iProver_top
    | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_2387,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_2973,plain,
    ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != X1_45
    | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = sK2
    | sK2 != X1_45 ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3031,plain,
    ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != k2_struct_0(k1_pre_topc(X0_44,X0_45))
    | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = sK2
    | sK2 != k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_2973])).

cnf(c_3033,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2
    | sK2 != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3031])).

cnf(c_3032,plain,
    ( ~ l1_pre_topc(k1_pre_topc(X0_44,X0_45))
    | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_2366])).

cnf(c_3035,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
    | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_3032])).

cnf(c_3115,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3113])).

cnf(c_3157,plain,
    ( k2_struct_0(k1_pre_topc(X0_44,X0_45)) != X1_45
    | sK2 != X1_45
    | sK2 = k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3158,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3157])).

cnf(c_3123,plain,
    ( u1_struct_0(X0_44) != X0_45
    | sK2 != X0_45
    | sK2 = u1_struct_0(X0_44) ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_3298,plain,
    ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2
    | sK2 = u1_struct_0(k1_pre_topc(X0_44,X0_45))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_3299,plain,
    ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
    | sK2 = u1_struct_0(k1_pre_topc(sK1,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3298])).

cnf(c_2398,plain,
    ( ~ v3_tex_2(X0_45,X0_44)
    | v3_tex_2(X1_45,X1_44)
    | X1_45 != X0_45
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_3398,plain,
    ( ~ v3_tex_2(X0_45,X0_44)
    | v3_tex_2(sK0(X1_44,k1_pre_topc(X1_44,X1_45)),X1_44)
    | sK0(X1_44,k1_pre_topc(X1_44,X1_45)) != X0_45
    | X1_44 != X0_44 ),
    inference(instantiation,[status(thm)],[c_2398])).

cnf(c_3399,plain,
    ( sK0(X0_44,k1_pre_topc(X0_44,X0_45)) != X1_45
    | X0_44 != X1_44
    | v3_tex_2(X1_45,X1_44) != iProver_top
    | v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3398])).

cnf(c_3401,plain,
    ( sK0(sK1,k1_pre_topc(sK1,sK2)) != sK2
    | sK1 != sK1
    | v3_tex_2(sK0(sK1,k1_pre_topc(sK1,sK2)),sK1) = iProver_top
    | v3_tex_2(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3399])).

cnf(c_9,plain,
    ( v4_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2376,plain,
    ( v4_tex_2(X0_44,X1_44)
    | ~ m1_pre_topc(X0_44,X1_44)
    | v2_struct_0(X1_44)
    | ~ l1_pre_topc(X1_44)
    | sK0(X1_44,X0_44) = u1_struct_0(X0_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_2750,plain,
    ( sK0(X0_44,X1_44) = u1_struct_0(X1_44)
    | v4_tex_2(X1_44,X0_44) = iProver_top
    | m1_pre_topc(X1_44,X0_44) != iProver_top
    | v2_struct_0(X0_44) = iProver_top
    | l1_pre_topc(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2376])).

cnf(c_3348,plain,
    ( sK0(sK1,k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
    | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3316,c_2750])).

cnf(c_3656,plain,
    ( sK0(sK1,k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
    | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3348,c_18,c_19])).

cnf(c_3712,plain,
    ( X0_45 != X1_45
    | sK0(X0_44,k1_pre_topc(X0_44,X2_45)) != X1_45
    | sK0(X0_44,k1_pre_topc(X0_44,X2_45)) = X0_45 ),
    inference(instantiation,[status(thm)],[c_2387])).

cnf(c_4077,plain,
    ( X0_45 != u1_struct_0(k1_pre_topc(X0_44,X1_45))
    | sK0(X0_44,k1_pre_topc(X0_44,X1_45)) = X0_45
    | sK0(X0_44,k1_pre_topc(X0_44,X1_45)) != u1_struct_0(k1_pre_topc(X0_44,X1_45)) ),
    inference(instantiation,[status(thm)],[c_3712])).

cnf(c_4078,plain,
    ( sK0(sK1,k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
    | sK0(sK1,k1_pre_topc(sK1,sK2)) = sK2
    | sK2 != u1_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_4077])).

cnf(c_4240,plain,
    ( v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4127,c_18,c_16,c_19,c_14,c_21,c_22,c_2411,c_2412,c_2418,c_2419,c_2422,c_2438,c_2912,c_2945,c_3033,c_3035,c_3115,c_3158,c_3299,c_3401,c_3656,c_4078])).

cnf(c_4242,plain,
    ( v2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4240])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4465,c_4242,c_3115,c_2438,c_2418,c_14,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.96/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/1.00  
% 1.96/1.00  ------  iProver source info
% 1.96/1.00  
% 1.96/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.96/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/1.00  git: non_committed_changes: false
% 1.96/1.00  git: last_make_outside_of_git: false
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     num_symb
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       true
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  ------ Parsing...
% 1.96/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/1.00  ------ Proving...
% 1.96/1.00  ------ Problem Properties 
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  clauses                                 16
% 1.96/1.00  conjectures                             5
% 1.96/1.00  EPR                                     4
% 1.96/1.00  Horn                                    12
% 1.96/1.00  unary                                   4
% 1.96/1.00  binary                                  1
% 1.96/1.00  lits                                    52
% 1.96/1.00  lits eq                                 6
% 1.96/1.00  fd_pure                                 0
% 1.96/1.00  fd_pseudo                               0
% 1.96/1.00  fd_cond                                 0
% 1.96/1.00  fd_pseudo_cond                          0
% 1.96/1.00  AC symbols                              0
% 1.96/1.00  
% 1.96/1.00  ------ Schedule dynamic 5 is on 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ 
% 1.96/1.00  Current options:
% 1.96/1.00  ------ 
% 1.96/1.00  
% 1.96/1.00  ------ Input Options
% 1.96/1.00  
% 1.96/1.00  --out_options                           all
% 1.96/1.00  --tptp_safe_out                         true
% 1.96/1.00  --problem_path                          ""
% 1.96/1.00  --include_path                          ""
% 1.96/1.00  --clausifier                            res/vclausify_rel
% 1.96/1.00  --clausifier_options                    --mode clausify
% 1.96/1.00  --stdin                                 false
% 1.96/1.00  --stats_out                             all
% 1.96/1.00  
% 1.96/1.00  ------ General Options
% 1.96/1.00  
% 1.96/1.00  --fof                                   false
% 1.96/1.00  --time_out_real                         305.
% 1.96/1.00  --time_out_virtual                      -1.
% 1.96/1.00  --symbol_type_check                     false
% 1.96/1.00  --clausify_out                          false
% 1.96/1.00  --sig_cnt_out                           false
% 1.96/1.00  --trig_cnt_out                          false
% 1.96/1.00  --trig_cnt_out_tolerance                1.
% 1.96/1.00  --trig_cnt_out_sk_spl                   false
% 1.96/1.00  --abstr_cl_out                          false
% 1.96/1.00  
% 1.96/1.00  ------ Global Options
% 1.96/1.00  
% 1.96/1.00  --schedule                              default
% 1.96/1.00  --add_important_lit                     false
% 1.96/1.00  --prop_solver_per_cl                    1000
% 1.96/1.00  --min_unsat_core                        false
% 1.96/1.00  --soft_assumptions                      false
% 1.96/1.00  --soft_lemma_size                       3
% 1.96/1.00  --prop_impl_unit_size                   0
% 1.96/1.00  --prop_impl_unit                        []
% 1.96/1.00  --share_sel_clauses                     true
% 1.96/1.00  --reset_solvers                         false
% 1.96/1.00  --bc_imp_inh                            [conj_cone]
% 1.96/1.00  --conj_cone_tolerance                   3.
% 1.96/1.00  --extra_neg_conj                        none
% 1.96/1.00  --large_theory_mode                     true
% 1.96/1.00  --prolific_symb_bound                   200
% 1.96/1.00  --lt_threshold                          2000
% 1.96/1.00  --clause_weak_htbl                      true
% 1.96/1.00  --gc_record_bc_elim                     false
% 1.96/1.00  
% 1.96/1.00  ------ Preprocessing Options
% 1.96/1.00  
% 1.96/1.00  --preprocessing_flag                    true
% 1.96/1.00  --time_out_prep_mult                    0.1
% 1.96/1.00  --splitting_mode                        input
% 1.96/1.00  --splitting_grd                         true
% 1.96/1.00  --splitting_cvd                         false
% 1.96/1.00  --splitting_cvd_svl                     false
% 1.96/1.00  --splitting_nvd                         32
% 1.96/1.00  --sub_typing                            true
% 1.96/1.00  --prep_gs_sim                           true
% 1.96/1.00  --prep_unflatten                        true
% 1.96/1.00  --prep_res_sim                          true
% 1.96/1.00  --prep_upred                            true
% 1.96/1.00  --prep_sem_filter                       exhaustive
% 1.96/1.00  --prep_sem_filter_out                   false
% 1.96/1.00  --pred_elim                             true
% 1.96/1.00  --res_sim_input                         true
% 1.96/1.00  --eq_ax_congr_red                       true
% 1.96/1.00  --pure_diseq_elim                       true
% 1.96/1.00  --brand_transform                       false
% 1.96/1.00  --non_eq_to_eq                          false
% 1.96/1.00  --prep_def_merge                        true
% 1.96/1.00  --prep_def_merge_prop_impl              false
% 1.96/1.00  --prep_def_merge_mbd                    true
% 1.96/1.00  --prep_def_merge_tr_red                 false
% 1.96/1.00  --prep_def_merge_tr_cl                  false
% 1.96/1.00  --smt_preprocessing                     true
% 1.96/1.00  --smt_ac_axioms                         fast
% 1.96/1.00  --preprocessed_out                      false
% 1.96/1.00  --preprocessed_stats                    false
% 1.96/1.00  
% 1.96/1.00  ------ Abstraction refinement Options
% 1.96/1.00  
% 1.96/1.00  --abstr_ref                             []
% 1.96/1.00  --abstr_ref_prep                        false
% 1.96/1.00  --abstr_ref_until_sat                   false
% 1.96/1.00  --abstr_ref_sig_restrict                funpre
% 1.96/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/1.00  --abstr_ref_under                       []
% 1.96/1.00  
% 1.96/1.00  ------ SAT Options
% 1.96/1.00  
% 1.96/1.00  --sat_mode                              false
% 1.96/1.00  --sat_fm_restart_options                ""
% 1.96/1.00  --sat_gr_def                            false
% 1.96/1.00  --sat_epr_types                         true
% 1.96/1.00  --sat_non_cyclic_types                  false
% 1.96/1.00  --sat_finite_models                     false
% 1.96/1.00  --sat_fm_lemmas                         false
% 1.96/1.00  --sat_fm_prep                           false
% 1.96/1.00  --sat_fm_uc_incr                        true
% 1.96/1.00  --sat_out_model                         small
% 1.96/1.00  --sat_out_clauses                       false
% 1.96/1.00  
% 1.96/1.00  ------ QBF Options
% 1.96/1.00  
% 1.96/1.00  --qbf_mode                              false
% 1.96/1.00  --qbf_elim_univ                         false
% 1.96/1.00  --qbf_dom_inst                          none
% 1.96/1.00  --qbf_dom_pre_inst                      false
% 1.96/1.00  --qbf_sk_in                             false
% 1.96/1.00  --qbf_pred_elim                         true
% 1.96/1.00  --qbf_split                             512
% 1.96/1.00  
% 1.96/1.00  ------ BMC1 Options
% 1.96/1.00  
% 1.96/1.00  --bmc1_incremental                      false
% 1.96/1.00  --bmc1_axioms                           reachable_all
% 1.96/1.00  --bmc1_min_bound                        0
% 1.96/1.00  --bmc1_max_bound                        -1
% 1.96/1.00  --bmc1_max_bound_default                -1
% 1.96/1.00  --bmc1_symbol_reachability              true
% 1.96/1.00  --bmc1_property_lemmas                  false
% 1.96/1.00  --bmc1_k_induction                      false
% 1.96/1.00  --bmc1_non_equiv_states                 false
% 1.96/1.00  --bmc1_deadlock                         false
% 1.96/1.00  --bmc1_ucm                              false
% 1.96/1.00  --bmc1_add_unsat_core                   none
% 1.96/1.00  --bmc1_unsat_core_children              false
% 1.96/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/1.00  --bmc1_out_stat                         full
% 1.96/1.00  --bmc1_ground_init                      false
% 1.96/1.00  --bmc1_pre_inst_next_state              false
% 1.96/1.00  --bmc1_pre_inst_state                   false
% 1.96/1.00  --bmc1_pre_inst_reach_state             false
% 1.96/1.00  --bmc1_out_unsat_core                   false
% 1.96/1.00  --bmc1_aig_witness_out                  false
% 1.96/1.00  --bmc1_verbose                          false
% 1.96/1.00  --bmc1_dump_clauses_tptp                false
% 1.96/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.96/1.00  --bmc1_dump_file                        -
% 1.96/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.96/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.96/1.00  --bmc1_ucm_extend_mode                  1
% 1.96/1.00  --bmc1_ucm_init_mode                    2
% 1.96/1.00  --bmc1_ucm_cone_mode                    none
% 1.96/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.96/1.00  --bmc1_ucm_relax_model                  4
% 1.96/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.96/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/1.00  --bmc1_ucm_layered_model                none
% 1.96/1.00  --bmc1_ucm_max_lemma_size               10
% 1.96/1.00  
% 1.96/1.00  ------ AIG Options
% 1.96/1.00  
% 1.96/1.00  --aig_mode                              false
% 1.96/1.00  
% 1.96/1.00  ------ Instantiation Options
% 1.96/1.00  
% 1.96/1.00  --instantiation_flag                    true
% 1.96/1.00  --inst_sos_flag                         false
% 1.96/1.00  --inst_sos_phase                        true
% 1.96/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/1.00  --inst_lit_sel_side                     none
% 1.96/1.00  --inst_solver_per_active                1400
% 1.96/1.00  --inst_solver_calls_frac                1.
% 1.96/1.00  --inst_passive_queue_type               priority_queues
% 1.96/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/1.00  --inst_passive_queues_freq              [25;2]
% 1.96/1.00  --inst_dismatching                      true
% 1.96/1.00  --inst_eager_unprocessed_to_passive     true
% 1.96/1.00  --inst_prop_sim_given                   true
% 1.96/1.00  --inst_prop_sim_new                     false
% 1.96/1.00  --inst_subs_new                         false
% 1.96/1.00  --inst_eq_res_simp                      false
% 1.96/1.00  --inst_subs_given                       false
% 1.96/1.00  --inst_orphan_elimination               true
% 1.96/1.00  --inst_learning_loop_flag               true
% 1.96/1.00  --inst_learning_start                   3000
% 1.96/1.00  --inst_learning_factor                  2
% 1.96/1.00  --inst_start_prop_sim_after_learn       3
% 1.96/1.00  --inst_sel_renew                        solver
% 1.96/1.00  --inst_lit_activity_flag                true
% 1.96/1.00  --inst_restr_to_given                   false
% 1.96/1.00  --inst_activity_threshold               500
% 1.96/1.00  --inst_out_proof                        true
% 1.96/1.00  
% 1.96/1.00  ------ Resolution Options
% 1.96/1.00  
% 1.96/1.00  --resolution_flag                       false
% 1.96/1.00  --res_lit_sel                           adaptive
% 1.96/1.00  --res_lit_sel_side                      none
% 1.96/1.00  --res_ordering                          kbo
% 1.96/1.00  --res_to_prop_solver                    active
% 1.96/1.00  --res_prop_simpl_new                    false
% 1.96/1.00  --res_prop_simpl_given                  true
% 1.96/1.00  --res_passive_queue_type                priority_queues
% 1.96/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/1.00  --res_passive_queues_freq               [15;5]
% 1.96/1.00  --res_forward_subs                      full
% 1.96/1.00  --res_backward_subs                     full
% 1.96/1.00  --res_forward_subs_resolution           true
% 1.96/1.00  --res_backward_subs_resolution          true
% 1.96/1.00  --res_orphan_elimination                true
% 1.96/1.00  --res_time_limit                        2.
% 1.96/1.00  --res_out_proof                         true
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Options
% 1.96/1.00  
% 1.96/1.00  --superposition_flag                    true
% 1.96/1.00  --sup_passive_queue_type                priority_queues
% 1.96/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.96/1.00  --demod_completeness_check              fast
% 1.96/1.00  --demod_use_ground                      true
% 1.96/1.00  --sup_to_prop_solver                    passive
% 1.96/1.00  --sup_prop_simpl_new                    true
% 1.96/1.00  --sup_prop_simpl_given                  true
% 1.96/1.00  --sup_fun_splitting                     false
% 1.96/1.00  --sup_smt_interval                      50000
% 1.96/1.00  
% 1.96/1.00  ------ Superposition Simplification Setup
% 1.96/1.00  
% 1.96/1.00  --sup_indices_passive                   []
% 1.96/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_full_bw                           [BwDemod]
% 1.96/1.00  --sup_immed_triv                        [TrivRules]
% 1.96/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_immed_bw_main                     []
% 1.96/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/1.00  
% 1.96/1.00  ------ Combination Options
% 1.96/1.00  
% 1.96/1.00  --comb_res_mult                         3
% 1.96/1.00  --comb_sup_mult                         2
% 1.96/1.00  --comb_inst_mult                        10
% 1.96/1.00  
% 1.96/1.00  ------ Debug Options
% 1.96/1.00  
% 1.96/1.00  --dbg_backtrace                         false
% 1.96/1.00  --dbg_dump_prop_clauses                 false
% 1.96/1.00  --dbg_dump_prop_clauses_file            -
% 1.96/1.00  --dbg_out_stat                          false
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  ------ Proving...
% 1.96/1.00  
% 1.96/1.00  
% 1.96/1.00  % SZS status Theorem for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/1.00  
% 1.96/1.00  fof(f4,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f16,plain,(
% 1.96/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f4])).
% 1.96/1.00  
% 1.96/1.00  fof(f37,plain,(
% 1.96/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f16])).
% 1.96/1.00  
% 1.96/1.00  fof(f6,axiom,(
% 1.96/1.00    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(k2_struct_0(X0)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f18,plain,(
% 1.96/1.00    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f6])).
% 1.96/1.00  
% 1.96/1.00  fof(f19,plain,(
% 1.96/1.00    ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f18])).
% 1.96/1.00  
% 1.96/1.00  fof(f39,plain,(
% 1.96/1.00    ( ! [X0] : (v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f19])).
% 1.96/1.00  
% 1.96/1.00  fof(f8,conjecture,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f9,negated_conjecture,(
% 1.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 1.96/1.00    inference(negated_conjecture,[],[f8])).
% 1.96/1.00  
% 1.96/1.00  fof(f10,plain,(
% 1.96/1.00    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => ~(u1_struct_0(X2) = X1 & v4_tex_2(X2,X0))) & v3_tex_2(X1,X0))))),
% 1.96/1.00    inference(pure_predicate_removal,[],[f9])).
% 1.96/1.00  
% 1.96/1.00  fof(f22,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : ((! [X2] : ((u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0)) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2))) & v3_tex_2(X1,X0)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f10])).
% 1.96/1.00  
% 1.96/1.00  fof(f23,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f22])).
% 1.96/1.00  
% 1.96/1.00  fof(f30,plain,(
% 1.96/1.00    ( ! [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (! [X2] : (u1_struct_0(X2) != sK2 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(sK2))) )),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f29,plain,(
% 1.96/1.00    ? [X0] : (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,X0) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (! [X2] : (u1_struct_0(X2) != X1 | ~v4_tex_2(X2,sK1) | ~m1_pre_topc(X2,sK1) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f31,plain,(
% 1.96/1.00    (! [X2] : (u1_struct_0(X2) != sK2 | ~v4_tex_2(X2,sK1) | ~m1_pre_topc(X2,sK1) | ~v1_pre_topc(X2) | v2_struct_0(X2)) & v3_tex_2(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) & ~v1_xboole_0(sK2)) & l1_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f30,f29])).
% 1.96/1.00  
% 1.96/1.00  fof(f46,plain,(
% 1.96/1.00    ~v1_xboole_0(sK2)),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f45,plain,(
% 1.96/1.00    l1_pre_topc(sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f2,axiom,(
% 1.96/1.00    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f13,plain,(
% 1.96/1.00    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f2])).
% 1.96/1.00  
% 1.96/1.00  fof(f34,plain,(
% 1.96/1.00    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f13])).
% 1.96/1.00  
% 1.96/1.00  fof(f47,plain,(
% 1.96/1.00    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f3,axiom,(
% 1.96/1.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f14,plain,(
% 1.96/1.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f3])).
% 1.96/1.00  
% 1.96/1.00  fof(f15,plain,(
% 1.96/1.00    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(flattening,[],[f14])).
% 1.96/1.00  
% 1.96/1.00  fof(f36,plain,(
% 1.96/1.00    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f5,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f17,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f5])).
% 1.96/1.00  
% 1.96/1.00  fof(f38,plain,(
% 1.96/1.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f17])).
% 1.96/1.00  
% 1.96/1.00  fof(f49,plain,(
% 1.96/1.00    ( ! [X2] : (u1_struct_0(X2) != sK2 | ~v4_tex_2(X2,sK1) | ~m1_pre_topc(X2,sK1) | ~v1_pre_topc(X2) | v2_struct_0(X2)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f44,plain,(
% 1.96/1.00    ~v2_struct_0(sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f48,plain,(
% 1.96/1.00    v3_tex_2(sK2,sK1)),
% 1.96/1.00    inference(cnf_transformation,[],[f31])).
% 1.96/1.00  
% 1.96/1.00  fof(f35,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f15])).
% 1.96/1.00  
% 1.96/1.00  fof(f1,axiom,(
% 1.96/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f11,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(ennf_transformation,[],[f1])).
% 1.96/1.00  
% 1.96/1.00  fof(f12,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(flattening,[],[f11])).
% 1.96/1.00  
% 1.96/1.00  fof(f24,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f12])).
% 1.96/1.00  
% 1.96/1.00  fof(f32,plain,(
% 1.96/1.00    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f24])).
% 1.96/1.00  
% 1.96/1.00  fof(f51,plain,(
% 1.96/1.00    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.96/1.00    inference(equality_resolution,[],[f32])).
% 1.96/1.00  
% 1.96/1.00  fof(f7,axiom,(
% 1.96/1.00    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v4_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_tex_2(X2,X0))))))),
% 1.96/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/1.00  
% 1.96/1.00  fof(f20,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : ((v3_tex_2(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.96/1.00    inference(ennf_transformation,[],[f7])).
% 1.96/1.00  
% 1.96/1.00  fof(f21,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : ((v4_tex_2(X1,X0) <=> ! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(flattening,[],[f20])).
% 1.96/1.00  
% 1.96/1.00  fof(f25,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_tex_2(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(nnf_transformation,[],[f21])).
% 1.96/1.00  
% 1.96/1.00  fof(f26,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | ? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(rectify,[],[f25])).
% 1.96/1.00  
% 1.96/1.00  fof(f27,plain,(
% 1.96/1.00    ! [X1,X0] : (? [X2] : (~v3_tex_2(X2,X0) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.96/1.00    introduced(choice_axiom,[])).
% 1.96/1.00  
% 1.96/1.00  fof(f28,plain,(
% 1.96/1.00    ! [X0] : (! [X1] : (((v4_tex_2(X1,X0) | (~v3_tex_2(sK0(X0,X1),X0) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_tex_2(X3,X0) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.96/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 1.96/1.00  
% 1.96/1.00  fof(f43,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v4_tex_2(X1,X0) | ~v3_tex_2(sK0(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  fof(f42,plain,(
% 1.96/1.00    ( ! [X0,X1] : (v4_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.96/1.00    inference(cnf_transformation,[],[f28])).
% 1.96/1.00  
% 1.96/1.00  cnf(c_5,plain,
% 1.96/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f37]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_7,plain,
% 1.96/1.00      ( ~ v2_struct_0(X0)
% 1.96/1.00      | v1_xboole_0(k2_struct_0(X0))
% 1.96/1.00      | ~ l1_struct_0(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f39]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_15,negated_conjecture,
% 1.96/1.00      ( ~ v1_xboole_0(sK2) ),
% 1.96/1.00      inference(cnf_transformation,[],[f46]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_207,plain,
% 1.96/1.00      ( ~ v2_struct_0(X0) | ~ l1_struct_0(X0) | k2_struct_0(X0) != sK2 ),
% 1.96/1.00      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_223,plain,
% 1.96/1.00      ( ~ v2_struct_0(X0) | ~ l1_pre_topc(X0) | k2_struct_0(X0) != sK2 ),
% 1.96/1.00      inference(resolution,[status(thm)],[c_5,c_207]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2367,plain,
% 1.96/1.00      ( ~ v2_struct_0(X0_44)
% 1.96/1.00      | ~ l1_pre_topc(X0_44)
% 1.96/1.00      | k2_struct_0(X0_44) != sK2 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_223]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4463,plain,
% 1.96/1.00      ( ~ v2_struct_0(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | ~ l1_pre_topc(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | k2_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2367]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4465,plain,
% 1.96/1.00      ( ~ v2_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.00      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
% 1.96/1.00      | k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_4463]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_16,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f45]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2370,negated_conjecture,
% 1.96/1.00      ( l1_pre_topc(sK1) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2756,plain,
% 1.96/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2370]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2,plain,
% 1.96/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f34]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_235,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.96/1.00      inference(resolution,[status(thm)],[c_5,c_2]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2366,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X0_44) | u1_struct_0(X0_44) = k2_struct_0(X0_44) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_235]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2760,plain,
% 1.96/1.00      ( u1_struct_0(X0_44) = k2_struct_0(X0_44)
% 1.96/1.00      | l1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2366]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3004,plain,
% 1.96/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_2756,c_2760]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_14,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.96/1.00      inference(cnf_transformation,[],[f47]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2371,negated_conjecture,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2755,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2371]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3006,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 1.96/1.00      inference(demodulation,[status(thm)],[c_3004,c_2755]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 1.96/1.00      | ~ l1_pre_topc(X1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f36]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2380,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44)
% 1.96/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2746,plain,
% 1.96/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
% 1.96/1.00      | l1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3150,plain,
% 1.96/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_3004,c_2746]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_19,plain,
% 1.96/1.00      ( l1_pre_topc(sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3308,plain,
% 1.96/1.00      ( m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top
% 1.96/1.00      | m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_3150,c_19]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3309,plain,
% 1.96/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_struct_0(sK1))) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,X0_45),sK1) = iProver_top ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_3308]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3316,plain,
% 1.96/1.00      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_3006,c_3309]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_6,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f38]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2378,plain,
% 1.96/1.00      ( ~ m1_pre_topc(X0_44,X1_44)
% 1.96/1.00      | ~ l1_pre_topc(X1_44)
% 1.96/1.00      | l1_pre_topc(X0_44) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2748,plain,
% 1.96/1.00      ( m1_pre_topc(X0_44,X1_44) != iProver_top
% 1.96/1.00      | l1_pre_topc(X1_44) != iProver_top
% 1.96/1.00      | l1_pre_topc(X0_44) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2378]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3347,plain,
% 1.96/1.00      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_3316,c_2748]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_21,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2417,plain,
% 1.96/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
% 1.96/1.00      | l1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2380]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2419,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2417]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3113,plain,
% 1.96/1.00      ( ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),X1_44)
% 1.96/1.00      | ~ l1_pre_topc(X1_44)
% 1.96/1.00      | l1_pre_topc(k1_pre_topc(X0_44,X0_45)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2378]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3114,plain,
% 1.96/1.00      ( m1_pre_topc(k1_pre_topc(X0_44,X0_45),X1_44) != iProver_top
% 1.96/1.00      | l1_pre_topc(X1_44) != iProver_top
% 1.96/1.00      | l1_pre_topc(k1_pre_topc(X0_44,X0_45)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_3113]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3116,plain,
% 1.96/1.00      ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3114]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3432,plain,
% 1.96/1.00      ( l1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_3347,c_19,c_21,c_2419,c_3116]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3437,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_3432,c_2760]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_12,negated_conjecture,
% 1.96/1.00      ( ~ v4_tex_2(X0,sK1)
% 1.96/1.00      | ~ m1_pre_topc(X0,sK1)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ v1_pre_topc(X0)
% 1.96/1.00      | u1_struct_0(X0) != sK2 ),
% 1.96/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2373,negated_conjecture,
% 1.96/1.00      ( ~ v4_tex_2(X0_44,sK1)
% 1.96/1.00      | ~ m1_pre_topc(X0_44,sK1)
% 1.96/1.00      | v2_struct_0(X0_44)
% 1.96/1.00      | ~ v1_pre_topc(X0_44)
% 1.96/1.00      | u1_struct_0(X0_44) != sK2 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2753,plain,
% 1.96/1.00      ( u1_struct_0(X0_44) != sK2
% 1.96/1.00      | v4_tex_2(X0_44,sK1) != iProver_top
% 1.96/1.00      | m1_pre_topc(X0_44,sK1) != iProver_top
% 1.96/1.00      | v2_struct_0(X0_44) = iProver_top
% 1.96/1.00      | v1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2373]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4127,plain,
% 1.96/1.00      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 1.96/1.00      | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 1.96/1.00      inference(superposition,[status(thm)],[c_3437,c_2753]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_17,negated_conjecture,
% 1.96/1.00      ( ~ v2_struct_0(sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f44]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_18,plain,
% 1.96/1.00      ( v2_struct_0(sK1) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_13,negated_conjecture,
% 1.96/1.00      ( v3_tex_2(sK2,sK1) ),
% 1.96/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_22,plain,
% 1.96/1.00      ( v3_tex_2(sK2,sK1) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2383,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2411,plain,
% 1.96/1.00      ( sK1 = sK1 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2383]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2384,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2412,plain,
% 1.96/1.00      ( sK2 = sK2 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2384]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2418,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 1.96/1.00      | ~ l1_pre_topc(sK1) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2380]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_4,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 1.96/1.00      inference(cnf_transformation,[],[f35]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2379,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 1.96/1.00      | ~ l1_pre_topc(X0_44)
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2420,plain,
% 1.96/1.00      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44))) != iProver_top
% 1.96/1.00      | l1_pre_topc(X0_44) != iProver_top
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) = iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2379]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2422,plain,
% 1.96/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2420]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_1,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ m1_pre_topc(k1_pre_topc(X1,X0),X1)
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 1.96/1.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 1.96/1.00      inference(cnf_transformation,[],[f51]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_111,plain,
% 1.96/1.00      ( ~ l1_pre_topc(X1)
% 1.96/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 1.96/1.00      inference(global_propositional_subsumption,
% 1.96/1.00                [status(thm)],
% 1.96/1.00                [c_1,c_4,c_3]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_112,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/1.00      | ~ l1_pre_topc(X1)
% 1.96/1.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 1.96/1.00      inference(renaming,[status(thm)],[c_111]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2368,plain,
% 1.96/1.00      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(X0_44)))
% 1.96/1.00      | ~ l1_pre_topc(X0_44)
% 1.96/1.00      | k2_struct_0(k1_pre_topc(X0_44,X0_45)) = X0_45 ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_112]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2438,plain,
% 1.96/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.96/1.00      | ~ l1_pre_topc(sK1)
% 1.96/1.00      | k2_struct_0(k1_pre_topc(sK1,sK2)) = sK2 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2368]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2909,plain,
% 1.96/1.00      ( ~ v4_tex_2(k1_pre_topc(X0_44,X0_45),sK1)
% 1.96/1.00      | ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),sK1)
% 1.96/1.00      | v2_struct_0(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | ~ v1_pre_topc(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2373]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2910,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2
% 1.96/1.00      | v4_tex_2(k1_pre_topc(X0_44,X0_45),sK1) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X0_44,X0_45),sK1) != iProver_top
% 1.96/1.00      | v2_struct_0(k1_pre_topc(X0_44,X0_45)) = iProver_top
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(X0_44,X0_45)) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2909]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2912,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 1.96/1.00      | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top
% 1.96/1.00      | v1_pre_topc(k1_pre_topc(sK1,sK2)) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2910]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_8,plain,
% 1.96/1.00      ( ~ v3_tex_2(sK0(X0,X1),X0)
% 1.96/1.00      | v4_tex_2(X1,X0)
% 1.96/1.00      | ~ m1_pre_topc(X1,X0)
% 1.96/1.00      | v2_struct_0(X0)
% 1.96/1.00      | ~ l1_pre_topc(X0) ),
% 1.96/1.00      inference(cnf_transformation,[],[f43]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2377,plain,
% 1.96/1.00      ( ~ v3_tex_2(sK0(X0_44,X1_44),X0_44)
% 1.96/1.00      | v4_tex_2(X1_44,X0_44)
% 1.96/1.00      | ~ m1_pre_topc(X1_44,X0_44)
% 1.96/1.00      | v2_struct_0(X0_44)
% 1.96/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.96/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2942,plain,
% 1.96/1.00      ( ~ v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44)
% 1.96/1.00      | v4_tex_2(k1_pre_topc(X0_44,X0_45),X0_44)
% 1.96/1.00      | ~ m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44)
% 1.96/1.00      | v2_struct_0(X0_44)
% 1.96/1.00      | ~ l1_pre_topc(X0_44) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2377]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2943,plain,
% 1.96/1.00      ( v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44) != iProver_top
% 1.96/1.00      | v4_tex_2(k1_pre_topc(X0_44,X0_45),X0_44) = iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(X0_44,X0_45),X0_44) != iProver_top
% 1.96/1.00      | v2_struct_0(X0_44) = iProver_top
% 1.96/1.00      | l1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.00      inference(predicate_to_equality,[status(thm)],[c_2942]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2945,plain,
% 1.96/1.00      ( v3_tex_2(sK0(sK1,k1_pre_topc(sK1,sK2)),sK1) != iProver_top
% 1.96/1.00      | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 1.96/1.00      | m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) != iProver_top
% 1.96/1.00      | v2_struct_0(sK1) = iProver_top
% 1.96/1.00      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2943]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2387,plain,
% 1.96/1.00      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.96/1.00      theory(equality) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_2973,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != X1_45
% 1.96/1.00      | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = sK2
% 1.96/1.00      | sK2 != X1_45 ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2387]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3031,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != k2_struct_0(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = sK2
% 1.96/1.00      | sK2 != k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2973]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3033,plain,
% 1.96/1.00      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != k2_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.00      | u1_struct_0(k1_pre_topc(sK1,sK2)) = sK2
% 1.96/1.00      | sK2 != k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3031]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3032,plain,
% 1.96/1.00      ( ~ l1_pre_topc(k1_pre_topc(X0_44,X0_45))
% 1.96/1.00      | u1_struct_0(k1_pre_topc(X0_44,X0_45)) = k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_2366]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3035,plain,
% 1.96/1.00      ( ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
% 1.96/1.00      | u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3032]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3115,plain,
% 1.96/1.00      ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
% 1.96/1.00      | l1_pre_topc(k1_pre_topc(sK1,sK2))
% 1.96/1.00      | ~ l1_pre_topc(sK1) ),
% 1.96/1.00      inference(instantiation,[status(thm)],[c_3113]) ).
% 1.96/1.00  
% 1.96/1.00  cnf(c_3157,plain,
% 1.96/1.00      ( k2_struct_0(k1_pre_topc(X0_44,X0_45)) != X1_45
% 1.96/1.00      | sK2 != X1_45
% 1.96/1.00      | sK2 = k2_struct_0(k1_pre_topc(X0_44,X0_45)) ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_2387]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3158,plain,
% 1.96/1.01      ( k2_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 1.96/1.01      | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.01      | sK2 != sK2 ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_3157]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3123,plain,
% 1.96/1.01      ( u1_struct_0(X0_44) != X0_45
% 1.96/1.01      | sK2 != X0_45
% 1.96/1.01      | sK2 = u1_struct_0(X0_44) ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_2387]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3298,plain,
% 1.96/1.01      ( u1_struct_0(k1_pre_topc(X0_44,X0_45)) != sK2
% 1.96/1.01      | sK2 = u1_struct_0(k1_pre_topc(X0_44,X0_45))
% 1.96/1.01      | sK2 != sK2 ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_3123]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3299,plain,
% 1.96/1.01      ( u1_struct_0(k1_pre_topc(sK1,sK2)) != sK2
% 1.96/1.01      | sK2 = u1_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.01      | sK2 != sK2 ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_3298]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2398,plain,
% 1.96/1.01      ( ~ v3_tex_2(X0_45,X0_44)
% 1.96/1.01      | v3_tex_2(X1_45,X1_44)
% 1.96/1.01      | X1_45 != X0_45
% 1.96/1.01      | X1_44 != X0_44 ),
% 1.96/1.01      theory(equality) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3398,plain,
% 1.96/1.01      ( ~ v3_tex_2(X0_45,X0_44)
% 1.96/1.01      | v3_tex_2(sK0(X1_44,k1_pre_topc(X1_44,X1_45)),X1_44)
% 1.96/1.01      | sK0(X1_44,k1_pre_topc(X1_44,X1_45)) != X0_45
% 1.96/1.01      | X1_44 != X0_44 ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_2398]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3399,plain,
% 1.96/1.01      ( sK0(X0_44,k1_pre_topc(X0_44,X0_45)) != X1_45
% 1.96/1.01      | X0_44 != X1_44
% 1.96/1.01      | v3_tex_2(X1_45,X1_44) != iProver_top
% 1.96/1.01      | v3_tex_2(sK0(X0_44,k1_pre_topc(X0_44,X0_45)),X0_44) = iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_3398]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3401,plain,
% 1.96/1.01      ( sK0(sK1,k1_pre_topc(sK1,sK2)) != sK2
% 1.96/1.01      | sK1 != sK1
% 1.96/1.01      | v3_tex_2(sK0(sK1,k1_pre_topc(sK1,sK2)),sK1) = iProver_top
% 1.96/1.01      | v3_tex_2(sK2,sK1) != iProver_top ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_3399]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_9,plain,
% 1.96/1.01      ( v4_tex_2(X0,X1)
% 1.96/1.01      | ~ m1_pre_topc(X0,X1)
% 1.96/1.01      | v2_struct_0(X1)
% 1.96/1.01      | ~ l1_pre_topc(X1)
% 1.96/1.01      | sK0(X1,X0) = u1_struct_0(X0) ),
% 1.96/1.01      inference(cnf_transformation,[],[f42]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2376,plain,
% 1.96/1.01      ( v4_tex_2(X0_44,X1_44)
% 1.96/1.01      | ~ m1_pre_topc(X0_44,X1_44)
% 1.96/1.01      | v2_struct_0(X1_44)
% 1.96/1.01      | ~ l1_pre_topc(X1_44)
% 1.96/1.01      | sK0(X1_44,X0_44) = u1_struct_0(X0_44) ),
% 1.96/1.01      inference(subtyping,[status(esa)],[c_9]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_2750,plain,
% 1.96/1.01      ( sK0(X0_44,X1_44) = u1_struct_0(X1_44)
% 1.96/1.01      | v4_tex_2(X1_44,X0_44) = iProver_top
% 1.96/1.01      | m1_pre_topc(X1_44,X0_44) != iProver_top
% 1.96/1.01      | v2_struct_0(X0_44) = iProver_top
% 1.96/1.01      | l1_pre_topc(X0_44) != iProver_top ),
% 1.96/1.01      inference(predicate_to_equality,[status(thm)],[c_2376]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3348,plain,
% 1.96/1.01      ( sK0(sK1,k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.01      | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top
% 1.96/1.01      | v2_struct_0(sK1) = iProver_top
% 1.96/1.01      | l1_pre_topc(sK1) != iProver_top ),
% 1.96/1.01      inference(superposition,[status(thm)],[c_3316,c_2750]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3656,plain,
% 1.96/1.01      ( sK0(sK1,k1_pre_topc(sK1,sK2)) = u1_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.01      | v4_tex_2(k1_pre_topc(sK1,sK2),sK1) = iProver_top ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_3348,c_18,c_19]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_3712,plain,
% 1.96/1.01      ( X0_45 != X1_45
% 1.96/1.01      | sK0(X0_44,k1_pre_topc(X0_44,X2_45)) != X1_45
% 1.96/1.01      | sK0(X0_44,k1_pre_topc(X0_44,X2_45)) = X0_45 ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_2387]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4077,plain,
% 1.96/1.01      ( X0_45 != u1_struct_0(k1_pre_topc(X0_44,X1_45))
% 1.96/1.01      | sK0(X0_44,k1_pre_topc(X0_44,X1_45)) = X0_45
% 1.96/1.01      | sK0(X0_44,k1_pre_topc(X0_44,X1_45)) != u1_struct_0(k1_pre_topc(X0_44,X1_45)) ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_3712]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4078,plain,
% 1.96/1.01      ( sK0(sK1,k1_pre_topc(sK1,sK2)) != u1_struct_0(k1_pre_topc(sK1,sK2))
% 1.96/1.01      | sK0(sK1,k1_pre_topc(sK1,sK2)) = sK2
% 1.96/1.01      | sK2 != u1_struct_0(k1_pre_topc(sK1,sK2)) ),
% 1.96/1.01      inference(instantiation,[status(thm)],[c_4077]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4240,plain,
% 1.96/1.01      ( v2_struct_0(k1_pre_topc(sK1,sK2)) = iProver_top ),
% 1.96/1.01      inference(global_propositional_subsumption,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_4127,c_18,c_16,c_19,c_14,c_21,c_22,c_2411,c_2412,
% 1.96/1.01                 c_2418,c_2419,c_2422,c_2438,c_2912,c_2945,c_3033,c_3035,
% 1.96/1.01                 c_3115,c_3158,c_3299,c_3401,c_3656,c_4078]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(c_4242,plain,
% 1.96/1.01      ( v2_struct_0(k1_pre_topc(sK1,sK2)) ),
% 1.96/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_4240]) ).
% 1.96/1.01  
% 1.96/1.01  cnf(contradiction,plain,
% 1.96/1.01      ( $false ),
% 1.96/1.01      inference(minisat,
% 1.96/1.01                [status(thm)],
% 1.96/1.01                [c_4465,c_4242,c_3115,c_2438,c_2418,c_14,c_16]) ).
% 1.96/1.01  
% 1.96/1.01  
% 1.96/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/1.01  
% 1.96/1.01  ------                               Statistics
% 1.96/1.01  
% 1.96/1.01  ------ General
% 1.96/1.01  
% 1.96/1.01  abstr_ref_over_cycles:                  0
% 1.96/1.01  abstr_ref_under_cycles:                 0
% 1.96/1.01  gc_basic_clause_elim:                   0
% 1.96/1.01  forced_gc_time:                         0
% 1.96/1.01  parsing_time:                           0.009
% 1.96/1.01  unif_index_cands_time:                  0.
% 1.96/1.01  unif_index_add_time:                    0.
% 1.96/1.01  orderings_time:                         0.
% 1.96/1.01  out_proof_time:                         0.013
% 1.96/1.01  total_time:                             0.168
% 1.96/1.01  num_of_symbols:                         47
% 1.96/1.01  num_of_terms:                           2925
% 1.96/1.01  
% 1.96/1.01  ------ Preprocessing
% 1.96/1.01  
% 1.96/1.01  num_of_splits:                          0
% 1.96/1.01  num_of_split_atoms:                     0
% 1.96/1.01  num_of_reused_defs:                     0
% 1.96/1.01  num_eq_ax_congr_red:                    13
% 1.96/1.01  num_of_sem_filtered_clauses:            1
% 1.96/1.01  num_of_subtypes:                        3
% 1.96/1.01  monotx_restored_types:                  0
% 1.96/1.01  sat_num_of_epr_types:                   0
% 1.96/1.01  sat_num_of_non_cyclic_types:            0
% 1.96/1.01  sat_guarded_non_collapsed_types:        2
% 1.96/1.01  num_pure_diseq_elim:                    0
% 1.96/1.01  simp_replaced_by:                       0
% 1.96/1.01  res_preprocessed:                       99
% 1.96/1.01  prep_upred:                             0
% 1.96/1.01  prep_unflattend:                        80
% 1.96/1.01  smt_new_axioms:                         0
% 1.96/1.01  pred_elim_cands:                        7
% 1.96/1.01  pred_elim:                              2
% 1.96/1.01  pred_elim_cl:                           2
% 1.96/1.01  pred_elim_cycles:                       14
% 1.96/1.01  merged_defs:                            0
% 1.96/1.01  merged_defs_ncl:                        0
% 1.96/1.01  bin_hyper_res:                          0
% 1.96/1.01  prep_cycles:                            4
% 1.96/1.01  pred_elim_time:                         0.035
% 1.96/1.01  splitting_time:                         0.
% 1.96/1.01  sem_filter_time:                        0.
% 1.96/1.01  monotx_time:                            0.
% 1.96/1.01  subtype_inf_time:                       0.
% 1.96/1.01  
% 1.96/1.01  ------ Problem properties
% 1.96/1.01  
% 1.96/1.01  clauses:                                16
% 1.96/1.01  conjectures:                            5
% 1.96/1.01  epr:                                    4
% 1.96/1.01  horn:                                   12
% 1.96/1.01  ground:                                 4
% 1.96/1.01  unary:                                  4
% 1.96/1.01  binary:                                 1
% 1.96/1.01  lits:                                   52
% 1.96/1.01  lits_eq:                                6
% 1.96/1.01  fd_pure:                                0
% 1.96/1.01  fd_pseudo:                              0
% 1.96/1.01  fd_cond:                                0
% 1.96/1.01  fd_pseudo_cond:                         0
% 1.96/1.01  ac_symbols:                             0
% 1.96/1.01  
% 1.96/1.01  ------ Propositional Solver
% 1.96/1.01  
% 1.96/1.01  prop_solver_calls:                      28
% 1.96/1.01  prop_fast_solver_calls:                 1259
% 1.96/1.01  smt_solver_calls:                       0
% 1.96/1.01  smt_fast_solver_calls:                  0
% 1.96/1.01  prop_num_of_clauses:                    923
% 1.96/1.01  prop_preprocess_simplified:             4114
% 1.96/1.01  prop_fo_subsumed:                       48
% 1.96/1.01  prop_solver_time:                       0.
% 1.96/1.01  smt_solver_time:                        0.
% 1.96/1.01  smt_fast_solver_time:                   0.
% 1.96/1.01  prop_fast_solver_time:                  0.
% 1.96/1.01  prop_unsat_core_time:                   0.
% 1.96/1.01  
% 1.96/1.01  ------ QBF
% 1.96/1.01  
% 1.96/1.01  qbf_q_res:                              0
% 1.96/1.01  qbf_num_tautologies:                    0
% 1.96/1.01  qbf_prep_cycles:                        0
% 1.96/1.01  
% 1.96/1.01  ------ BMC1
% 1.96/1.01  
% 1.96/1.01  bmc1_current_bound:                     -1
% 1.96/1.01  bmc1_last_solved_bound:                 -1
% 1.96/1.01  bmc1_unsat_core_size:                   -1
% 1.96/1.01  bmc1_unsat_core_parents_size:           -1
% 1.96/1.01  bmc1_merge_next_fun:                    0
% 1.96/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.96/1.01  
% 1.96/1.01  ------ Instantiation
% 1.96/1.01  
% 1.96/1.01  inst_num_of_clauses:                    268
% 1.96/1.01  inst_num_in_passive:                    69
% 1.96/1.01  inst_num_in_active:                     162
% 1.96/1.01  inst_num_in_unprocessed:                36
% 1.96/1.01  inst_num_of_loops:                      193
% 1.96/1.01  inst_num_of_learning_restarts:          0
% 1.96/1.01  inst_num_moves_active_passive:          26
% 1.96/1.01  inst_lit_activity:                      0
% 1.96/1.01  inst_lit_activity_moves:                0
% 1.96/1.01  inst_num_tautologies:                   0
% 1.96/1.01  inst_num_prop_implied:                  0
% 1.96/1.01  inst_num_existing_simplified:           0
% 1.96/1.01  inst_num_eq_res_simplified:             0
% 1.96/1.01  inst_num_child_elim:                    0
% 1.96/1.01  inst_num_of_dismatching_blockings:      121
% 1.96/1.01  inst_num_of_non_proper_insts:           309
% 1.96/1.01  inst_num_of_duplicates:                 0
% 1.96/1.01  inst_inst_num_from_inst_to_res:         0
% 1.96/1.01  inst_dismatching_checking_time:         0.
% 1.96/1.01  
% 1.96/1.01  ------ Resolution
% 1.96/1.01  
% 1.96/1.01  res_num_of_clauses:                     0
% 1.96/1.01  res_num_in_passive:                     0
% 1.96/1.01  res_num_in_active:                      0
% 1.96/1.01  res_num_of_loops:                       103
% 1.96/1.01  res_forward_subset_subsumed:            14
% 1.96/1.01  res_backward_subset_subsumed:           2
% 1.96/1.01  res_forward_subsumed:                   0
% 1.96/1.01  res_backward_subsumed:                  0
% 1.96/1.01  res_forward_subsumption_resolution:     0
% 1.96/1.01  res_backward_subsumption_resolution:    0
% 1.96/1.01  res_clause_to_clause_subsumption:       102
% 1.96/1.01  res_orphan_elimination:                 0
% 1.96/1.01  res_tautology_del:                      29
% 1.96/1.01  res_num_eq_res_simplified:              0
% 1.96/1.01  res_num_sel_changes:                    0
% 1.96/1.01  res_moves_from_active_to_pass:          0
% 1.96/1.01  
% 1.96/1.01  ------ Superposition
% 1.96/1.01  
% 1.96/1.01  sup_time_total:                         0.
% 1.96/1.01  sup_time_generating:                    0.
% 1.96/1.01  sup_time_sim_full:                      0.
% 1.96/1.01  sup_time_sim_immed:                     0.
% 1.96/1.01  
% 1.96/1.01  sup_num_of_clauses:                     50
% 1.96/1.01  sup_num_in_active:                      36
% 1.96/1.01  sup_num_in_passive:                     14
% 1.96/1.01  sup_num_of_loops:                       38
% 1.96/1.01  sup_fw_superposition:                   14
% 1.96/1.01  sup_bw_superposition:                   22
% 1.96/1.01  sup_immediate_simplified:               6
% 1.96/1.01  sup_given_eliminated:                   0
% 1.96/1.01  comparisons_done:                       0
% 1.96/1.01  comparisons_avoided:                    0
% 1.96/1.01  
% 1.96/1.01  ------ Simplifications
% 1.96/1.01  
% 1.96/1.01  
% 1.96/1.01  sim_fw_subset_subsumed:                 2
% 1.96/1.01  sim_bw_subset_subsumed:                 0
% 1.96/1.01  sim_fw_subsumed:                        0
% 1.96/1.01  sim_bw_subsumed:                        0
% 1.96/1.01  sim_fw_subsumption_res:                 0
% 1.96/1.01  sim_bw_subsumption_res:                 0
% 1.96/1.01  sim_tautology_del:                      0
% 1.96/1.01  sim_eq_tautology_del:                   0
% 1.96/1.01  sim_eq_res_simp:                        0
% 1.96/1.01  sim_fw_demodulated:                     0
% 1.96/1.01  sim_bw_demodulated:                     2
% 1.96/1.01  sim_light_normalised:                   4
% 1.96/1.01  sim_joinable_taut:                      0
% 1.96/1.01  sim_joinable_simp:                      0
% 1.96/1.01  sim_ac_normalised:                      0
% 1.96/1.01  sim_smt_subsumption:                    0
% 1.96/1.01  
%------------------------------------------------------------------------------
