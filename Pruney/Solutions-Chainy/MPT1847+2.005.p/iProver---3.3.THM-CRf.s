%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:24 EST 2020

% Result     : Theorem 11.10s
% Output     : CNFRefutation 11.10s
% Verified   : 
% Statistics : Number of formulae       :  217 (1994 expanded)
%              Number of clauses        :  144 ( 637 expanded)
%              Number of leaves         :   20 ( 543 expanded)
%              Depth                    :   22
%              Number of atoms          :  608 (8801 expanded)
%              Number of equality atoms :  253 (2011 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tex_2(X2,X0)
          & v1_tex_2(X1,X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X2,X0) )
     => ( ~ v1_tex_2(sK3,X0)
        & v1_tex_2(X1,X0)
        & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ~ v1_tex_2(X2,X0)
            & v1_tex_2(sK2,X0)
            & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tex_2(X2,X0)
                & v1_tex_2(X1,X0)
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,sK1)
              & v1_tex_2(X1,sK1)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK1) )
          & m1_pre_topc(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ~ v1_tex_2(sK3,sK1)
    & v1_tex_2(sK2,sK1)
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_pre_topc(sK3,sK1)
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f45,f44,f43])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
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

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2374,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2381,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3322,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2374,c_2381])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3699,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3322,c_30])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_332,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_2370,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_3703,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3699,c_2370])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2386,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2390,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2386,c_3])).

cnf(c_9,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2383,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4285,plain,
    ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_2383])).

cnf(c_6640,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_4285])).

cnf(c_7105,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6640,c_30,c_3322])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_175,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15,c_12])).

cnf(c_176,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_175])).

cnf(c_2372,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_176])).

cnf(c_5920,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_2372])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2375,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3321,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_2381])).

cnf(c_3693,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_30])).

cnf(c_3697,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3693,c_2370])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3788,plain,
    ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_3697,c_26])).

cnf(c_3789,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_3788,c_3703])).

cnf(c_5925,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5920,c_3789])).

cnf(c_6176,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5925,c_30,c_3322])).

cnf(c_6177,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6176])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2380,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4270,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_2380])).

cnf(c_11573,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4270,c_30,c_3321])).

cnf(c_11574,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_11573])).

cnf(c_11579,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6177,c_11574])).

cnf(c_11592,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7105,c_11579])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2378,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2388,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3581,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_2388])).

cnf(c_7313,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_3581])).

cnf(c_66,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_20295,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7313,c_66])).

cnf(c_20296,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_20295])).

cnf(c_34835,plain,
    ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = u1_struct_0(sK3)
    | m1_pre_topc(sK3,k1_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_11592,c_20296])).

cnf(c_6643,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4285,c_2381])).

cnf(c_6768,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_6643])).

cnf(c_7009,plain,
    ( l1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6768,c_30,c_3322])).

cnf(c_7014,plain,
    ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_7009,c_2370])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_9])).

cnf(c_192,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_191])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_197,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_192,c_10])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_197])).

cnf(c_2371,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_198])).

cnf(c_4896,plain,
    ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2390,c_2371])).

cnf(c_6780,plain,
    ( k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3699,c_4896])).

cnf(c_6784,plain,
    ( k2_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6780,c_3703])).

cnf(c_7015,plain,
    ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_7014,c_6784])).

cnf(c_34844,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | m1_pre_topc(sK3,k1_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34835,c_3697,c_7015])).

cnf(c_2373,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3075,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2373,c_2370])).

cnf(c_3580,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3075,c_2378])).

cnf(c_4049,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3580,c_30])).

cnf(c_4050,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4049])).

cnf(c_4055,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_4050])).

cnf(c_31,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6434,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4055,c_31])).

cnf(c_20,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_552,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_553,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_555,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_29,c_27])).

cnf(c_2366,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_19,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_563,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_564,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_563])).

cnf(c_566,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_564,c_29,c_27])).

cnf(c_2392,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2366,c_566])).

cnf(c_3076,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3075,c_2392])).

cnf(c_22,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2377,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3448,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK1)
    | v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3076,c_2377])).

cnf(c_18,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_571,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_572,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_574,plain,
    ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_572,c_29,c_27])).

cnf(c_2365,plain,
    ( v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_574])).

cnf(c_2391,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2365,c_566])).

cnf(c_3077,plain,
    ( v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3075,c_2391])).

cnf(c_5356,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3448,c_3077])).

cnf(c_5358,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_5356,c_3697])).

cnf(c_6438,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6434,c_5358])).

cnf(c_6440,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3)
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6438,c_2388])).

cnf(c_6641,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_4285])).

cnf(c_7180,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6641,c_30,c_3321])).

cnf(c_5921,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_2372])).

cnf(c_12070,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5921,c_30,c_3321])).

cnf(c_12071,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_12070])).

cnf(c_4269,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_2380])).

cnf(c_4272,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4269,c_3789])).

cnf(c_4663,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4272,c_30,c_3322])).

cnf(c_4664,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_4663])).

cnf(c_12079,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12071,c_4664])).

cnf(c_12087,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7180,c_12079])).

cnf(c_6769,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_6643])).

cnf(c_7096,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6769,c_30,c_3321])).

cnf(c_7101,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_7096,c_2370])).

cnf(c_6779,plain,
    ( k2_struct_0(k1_pre_topc(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3693,c_4896])).

cnf(c_6785,plain,
    ( k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_6779,c_3697])).

cnf(c_7102,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7101,c_6785])).

cnf(c_3919,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3703,c_2378])).

cnf(c_8399,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3919,c_30,c_3322])).

cnf(c_8400,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8399])).

cnf(c_33550,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7102,c_8400])).

cnf(c_35381,plain,
    ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34844,c_6440,c_12087,c_33550])).

cnf(c_21,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_163,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21,c_16])).

cnf(c_164,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_163])).

cnf(c_25,negated_conjecture,
    ( v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_582,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_164,c_25])).

cnf(c_583,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_585,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_583,c_29,c_28])).

cnf(c_2364,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_585])).

cnf(c_3078,plain,
    ( v1_subset_1(u1_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3075,c_2364])).

cnf(c_3913,plain,
    ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3703,c_3078])).

cnf(c_5800,plain,
    ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3913,c_5358])).

cnf(c_35465,plain,
    ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_35381,c_5800])).

cnf(c_5,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2385,plain,
    ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2389,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2385,c_3])).

cnf(c_36857,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_35465,c_2389])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:05:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 11.10/2.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.10/2.01  
% 11.10/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.10/2.01  
% 11.10/2.01  ------  iProver source info
% 11.10/2.01  
% 11.10/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.10/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.10/2.01  git: non_committed_changes: false
% 11.10/2.01  git: last_make_outside_of_git: false
% 11.10/2.01  
% 11.10/2.01  ------ 
% 11.10/2.01  
% 11.10/2.01  ------ Input Options
% 11.10/2.01  
% 11.10/2.01  --out_options                           all
% 11.10/2.01  --tptp_safe_out                         true
% 11.10/2.01  --problem_path                          ""
% 11.10/2.01  --include_path                          ""
% 11.10/2.01  --clausifier                            res/vclausify_rel
% 11.10/2.01  --clausifier_options                    ""
% 11.10/2.01  --stdin                                 false
% 11.10/2.01  --stats_out                             all
% 11.10/2.01  
% 11.10/2.01  ------ General Options
% 11.10/2.01  
% 11.10/2.01  --fof                                   false
% 11.10/2.01  --time_out_real                         305.
% 11.10/2.01  --time_out_virtual                      -1.
% 11.10/2.01  --symbol_type_check                     false
% 11.10/2.01  --clausify_out                          false
% 11.10/2.01  --sig_cnt_out                           false
% 11.10/2.01  --trig_cnt_out                          false
% 11.10/2.01  --trig_cnt_out_tolerance                1.
% 11.10/2.01  --trig_cnt_out_sk_spl                   false
% 11.10/2.01  --abstr_cl_out                          false
% 11.10/2.01  
% 11.10/2.01  ------ Global Options
% 11.10/2.01  
% 11.10/2.01  --schedule                              default
% 11.10/2.01  --add_important_lit                     false
% 11.10/2.01  --prop_solver_per_cl                    1000
% 11.10/2.01  --min_unsat_core                        false
% 11.10/2.01  --soft_assumptions                      false
% 11.10/2.01  --soft_lemma_size                       3
% 11.10/2.01  --prop_impl_unit_size                   0
% 11.10/2.01  --prop_impl_unit                        []
% 11.10/2.01  --share_sel_clauses                     true
% 11.10/2.01  --reset_solvers                         false
% 11.10/2.01  --bc_imp_inh                            [conj_cone]
% 11.10/2.01  --conj_cone_tolerance                   3.
% 11.10/2.01  --extra_neg_conj                        none
% 11.10/2.01  --large_theory_mode                     true
% 11.10/2.01  --prolific_symb_bound                   200
% 11.10/2.01  --lt_threshold                          2000
% 11.10/2.01  --clause_weak_htbl                      true
% 11.10/2.01  --gc_record_bc_elim                     false
% 11.10/2.01  
% 11.10/2.01  ------ Preprocessing Options
% 11.10/2.01  
% 11.10/2.01  --preprocessing_flag                    true
% 11.10/2.01  --time_out_prep_mult                    0.1
% 11.10/2.01  --splitting_mode                        input
% 11.10/2.01  --splitting_grd                         true
% 11.10/2.01  --splitting_cvd                         false
% 11.10/2.01  --splitting_cvd_svl                     false
% 11.10/2.01  --splitting_nvd                         32
% 11.10/2.01  --sub_typing                            true
% 11.10/2.01  --prep_gs_sim                           true
% 11.10/2.01  --prep_unflatten                        true
% 11.10/2.01  --prep_res_sim                          true
% 11.10/2.01  --prep_upred                            true
% 11.10/2.01  --prep_sem_filter                       exhaustive
% 11.10/2.01  --prep_sem_filter_out                   false
% 11.10/2.01  --pred_elim                             true
% 11.10/2.01  --res_sim_input                         true
% 11.10/2.01  --eq_ax_congr_red                       true
% 11.10/2.01  --pure_diseq_elim                       true
% 11.10/2.01  --brand_transform                       false
% 11.10/2.01  --non_eq_to_eq                          false
% 11.10/2.01  --prep_def_merge                        true
% 11.10/2.01  --prep_def_merge_prop_impl              false
% 11.10/2.01  --prep_def_merge_mbd                    true
% 11.10/2.01  --prep_def_merge_tr_red                 false
% 11.10/2.01  --prep_def_merge_tr_cl                  false
% 11.10/2.01  --smt_preprocessing                     true
% 11.10/2.01  --smt_ac_axioms                         fast
% 11.10/2.01  --preprocessed_out                      false
% 11.10/2.01  --preprocessed_stats                    false
% 11.10/2.01  
% 11.10/2.01  ------ Abstraction refinement Options
% 11.10/2.01  
% 11.10/2.01  --abstr_ref                             []
% 11.10/2.01  --abstr_ref_prep                        false
% 11.10/2.01  --abstr_ref_until_sat                   false
% 11.10/2.01  --abstr_ref_sig_restrict                funpre
% 11.10/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.10/2.01  --abstr_ref_under                       []
% 11.10/2.01  
% 11.10/2.01  ------ SAT Options
% 11.10/2.01  
% 11.10/2.01  --sat_mode                              false
% 11.10/2.01  --sat_fm_restart_options                ""
% 11.10/2.01  --sat_gr_def                            false
% 11.10/2.01  --sat_epr_types                         true
% 11.10/2.01  --sat_non_cyclic_types                  false
% 11.10/2.01  --sat_finite_models                     false
% 11.10/2.01  --sat_fm_lemmas                         false
% 11.10/2.01  --sat_fm_prep                           false
% 11.10/2.01  --sat_fm_uc_incr                        true
% 11.10/2.01  --sat_out_model                         small
% 11.10/2.01  --sat_out_clauses                       false
% 11.10/2.01  
% 11.10/2.01  ------ QBF Options
% 11.10/2.01  
% 11.10/2.01  --qbf_mode                              false
% 11.10/2.01  --qbf_elim_univ                         false
% 11.10/2.01  --qbf_dom_inst                          none
% 11.10/2.01  --qbf_dom_pre_inst                      false
% 11.10/2.01  --qbf_sk_in                             false
% 11.10/2.01  --qbf_pred_elim                         true
% 11.10/2.01  --qbf_split                             512
% 11.10/2.01  
% 11.10/2.01  ------ BMC1 Options
% 11.10/2.01  
% 11.10/2.01  --bmc1_incremental                      false
% 11.10/2.01  --bmc1_axioms                           reachable_all
% 11.10/2.01  --bmc1_min_bound                        0
% 11.10/2.01  --bmc1_max_bound                        -1
% 11.10/2.01  --bmc1_max_bound_default                -1
% 11.10/2.01  --bmc1_symbol_reachability              true
% 11.10/2.01  --bmc1_property_lemmas                  false
% 11.10/2.01  --bmc1_k_induction                      false
% 11.10/2.01  --bmc1_non_equiv_states                 false
% 11.10/2.01  --bmc1_deadlock                         false
% 11.10/2.01  --bmc1_ucm                              false
% 11.10/2.01  --bmc1_add_unsat_core                   none
% 11.10/2.01  --bmc1_unsat_core_children              false
% 11.10/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.10/2.01  --bmc1_out_stat                         full
% 11.10/2.01  --bmc1_ground_init                      false
% 11.10/2.01  --bmc1_pre_inst_next_state              false
% 11.10/2.01  --bmc1_pre_inst_state                   false
% 11.10/2.01  --bmc1_pre_inst_reach_state             false
% 11.10/2.01  --bmc1_out_unsat_core                   false
% 11.10/2.01  --bmc1_aig_witness_out                  false
% 11.10/2.01  --bmc1_verbose                          false
% 11.10/2.01  --bmc1_dump_clauses_tptp                false
% 11.10/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.10/2.01  --bmc1_dump_file                        -
% 11.10/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.10/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.10/2.01  --bmc1_ucm_extend_mode                  1
% 11.10/2.01  --bmc1_ucm_init_mode                    2
% 11.10/2.01  --bmc1_ucm_cone_mode                    none
% 11.10/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.10/2.01  --bmc1_ucm_relax_model                  4
% 11.10/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.10/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.10/2.01  --bmc1_ucm_layered_model                none
% 11.10/2.01  --bmc1_ucm_max_lemma_size               10
% 11.10/2.01  
% 11.10/2.01  ------ AIG Options
% 11.10/2.01  
% 11.10/2.01  --aig_mode                              false
% 11.10/2.01  
% 11.10/2.01  ------ Instantiation Options
% 11.10/2.01  
% 11.10/2.01  --instantiation_flag                    true
% 11.10/2.01  --inst_sos_flag                         true
% 11.10/2.01  --inst_sos_phase                        true
% 11.10/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.10/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.10/2.01  --inst_lit_sel_side                     num_symb
% 11.10/2.01  --inst_solver_per_active                1400
% 11.10/2.01  --inst_solver_calls_frac                1.
% 11.10/2.01  --inst_passive_queue_type               priority_queues
% 11.10/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.10/2.01  --inst_passive_queues_freq              [25;2]
% 11.10/2.01  --inst_dismatching                      true
% 11.10/2.01  --inst_eager_unprocessed_to_passive     true
% 11.10/2.01  --inst_prop_sim_given                   true
% 11.10/2.01  --inst_prop_sim_new                     false
% 11.10/2.01  --inst_subs_new                         false
% 11.10/2.01  --inst_eq_res_simp                      false
% 11.10/2.01  --inst_subs_given                       false
% 11.10/2.01  --inst_orphan_elimination               true
% 11.10/2.01  --inst_learning_loop_flag               true
% 11.10/2.01  --inst_learning_start                   3000
% 11.10/2.01  --inst_learning_factor                  2
% 11.10/2.01  --inst_start_prop_sim_after_learn       3
% 11.10/2.01  --inst_sel_renew                        solver
% 11.10/2.01  --inst_lit_activity_flag                true
% 11.10/2.01  --inst_restr_to_given                   false
% 11.10/2.01  --inst_activity_threshold               500
% 11.10/2.01  --inst_out_proof                        true
% 11.10/2.01  
% 11.10/2.01  ------ Resolution Options
% 11.10/2.01  
% 11.10/2.01  --resolution_flag                       true
% 11.10/2.01  --res_lit_sel                           adaptive
% 11.10/2.01  --res_lit_sel_side                      none
% 11.10/2.01  --res_ordering                          kbo
% 11.10/2.01  --res_to_prop_solver                    active
% 11.10/2.01  --res_prop_simpl_new                    false
% 11.10/2.01  --res_prop_simpl_given                  true
% 11.10/2.01  --res_passive_queue_type                priority_queues
% 11.10/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.10/2.01  --res_passive_queues_freq               [15;5]
% 11.10/2.01  --res_forward_subs                      full
% 11.10/2.01  --res_backward_subs                     full
% 11.10/2.01  --res_forward_subs_resolution           true
% 11.10/2.01  --res_backward_subs_resolution          true
% 11.10/2.01  --res_orphan_elimination                true
% 11.10/2.01  --res_time_limit                        2.
% 11.10/2.01  --res_out_proof                         true
% 11.10/2.01  
% 11.10/2.01  ------ Superposition Options
% 11.10/2.01  
% 11.10/2.01  --superposition_flag                    true
% 11.10/2.01  --sup_passive_queue_type                priority_queues
% 11.10/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.10/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.10/2.01  --demod_completeness_check              fast
% 11.10/2.01  --demod_use_ground                      true
% 11.10/2.01  --sup_to_prop_solver                    passive
% 11.10/2.01  --sup_prop_simpl_new                    true
% 11.10/2.01  --sup_prop_simpl_given                  true
% 11.10/2.01  --sup_fun_splitting                     true
% 11.10/2.01  --sup_smt_interval                      50000
% 11.10/2.01  
% 11.10/2.01  ------ Superposition Simplification Setup
% 11.10/2.01  
% 11.10/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.10/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.10/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.10/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.10/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.10/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.10/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.10/2.01  --sup_immed_triv                        [TrivRules]
% 11.10/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_immed_bw_main                     []
% 11.10/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.10/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.10/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_input_bw                          []
% 11.10/2.01  
% 11.10/2.01  ------ Combination Options
% 11.10/2.01  
% 11.10/2.01  --comb_res_mult                         3
% 11.10/2.01  --comb_sup_mult                         2
% 11.10/2.01  --comb_inst_mult                        10
% 11.10/2.01  
% 11.10/2.01  ------ Debug Options
% 11.10/2.01  
% 11.10/2.01  --dbg_backtrace                         false
% 11.10/2.01  --dbg_dump_prop_clauses                 false
% 11.10/2.01  --dbg_dump_prop_clauses_file            -
% 11.10/2.01  --dbg_out_stat                          false
% 11.10/2.01  ------ Parsing...
% 11.10/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.10/2.01  
% 11.10/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.10/2.01  
% 11.10/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.10/2.01  
% 11.10/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.10/2.01  ------ Proving...
% 11.10/2.01  ------ Problem Properties 
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  clauses                                 29
% 11.10/2.01  conjectures                             4
% 11.10/2.01  EPR                                     7
% 11.10/2.01  Horn                                    26
% 11.10/2.01  unary                                   13
% 11.10/2.01  binary                                  2
% 11.10/2.01  lits                                    64
% 11.10/2.01  lits eq                                 10
% 11.10/2.01  fd_pure                                 0
% 11.10/2.01  fd_pseudo                               0
% 11.10/2.01  fd_cond                                 0
% 11.10/2.01  fd_pseudo_cond                          2
% 11.10/2.01  AC symbols                              0
% 11.10/2.01  
% 11.10/2.01  ------ Schedule dynamic 5 is on 
% 11.10/2.01  
% 11.10/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  ------ 
% 11.10/2.01  Current options:
% 11.10/2.01  ------ 
% 11.10/2.01  
% 11.10/2.01  ------ Input Options
% 11.10/2.01  
% 11.10/2.01  --out_options                           all
% 11.10/2.01  --tptp_safe_out                         true
% 11.10/2.01  --problem_path                          ""
% 11.10/2.01  --include_path                          ""
% 11.10/2.01  --clausifier                            res/vclausify_rel
% 11.10/2.01  --clausifier_options                    ""
% 11.10/2.01  --stdin                                 false
% 11.10/2.01  --stats_out                             all
% 11.10/2.01  
% 11.10/2.01  ------ General Options
% 11.10/2.01  
% 11.10/2.01  --fof                                   false
% 11.10/2.01  --time_out_real                         305.
% 11.10/2.01  --time_out_virtual                      -1.
% 11.10/2.01  --symbol_type_check                     false
% 11.10/2.01  --clausify_out                          false
% 11.10/2.01  --sig_cnt_out                           false
% 11.10/2.01  --trig_cnt_out                          false
% 11.10/2.01  --trig_cnt_out_tolerance                1.
% 11.10/2.01  --trig_cnt_out_sk_spl                   false
% 11.10/2.01  --abstr_cl_out                          false
% 11.10/2.01  
% 11.10/2.01  ------ Global Options
% 11.10/2.01  
% 11.10/2.01  --schedule                              default
% 11.10/2.01  --add_important_lit                     false
% 11.10/2.01  --prop_solver_per_cl                    1000
% 11.10/2.01  --min_unsat_core                        false
% 11.10/2.01  --soft_assumptions                      false
% 11.10/2.01  --soft_lemma_size                       3
% 11.10/2.01  --prop_impl_unit_size                   0
% 11.10/2.01  --prop_impl_unit                        []
% 11.10/2.01  --share_sel_clauses                     true
% 11.10/2.01  --reset_solvers                         false
% 11.10/2.01  --bc_imp_inh                            [conj_cone]
% 11.10/2.01  --conj_cone_tolerance                   3.
% 11.10/2.01  --extra_neg_conj                        none
% 11.10/2.01  --large_theory_mode                     true
% 11.10/2.01  --prolific_symb_bound                   200
% 11.10/2.01  --lt_threshold                          2000
% 11.10/2.01  --clause_weak_htbl                      true
% 11.10/2.01  --gc_record_bc_elim                     false
% 11.10/2.01  
% 11.10/2.01  ------ Preprocessing Options
% 11.10/2.01  
% 11.10/2.01  --preprocessing_flag                    true
% 11.10/2.01  --time_out_prep_mult                    0.1
% 11.10/2.01  --splitting_mode                        input
% 11.10/2.01  --splitting_grd                         true
% 11.10/2.01  --splitting_cvd                         false
% 11.10/2.01  --splitting_cvd_svl                     false
% 11.10/2.01  --splitting_nvd                         32
% 11.10/2.01  --sub_typing                            true
% 11.10/2.01  --prep_gs_sim                           true
% 11.10/2.01  --prep_unflatten                        true
% 11.10/2.01  --prep_res_sim                          true
% 11.10/2.01  --prep_upred                            true
% 11.10/2.01  --prep_sem_filter                       exhaustive
% 11.10/2.01  --prep_sem_filter_out                   false
% 11.10/2.01  --pred_elim                             true
% 11.10/2.01  --res_sim_input                         true
% 11.10/2.01  --eq_ax_congr_red                       true
% 11.10/2.01  --pure_diseq_elim                       true
% 11.10/2.01  --brand_transform                       false
% 11.10/2.01  --non_eq_to_eq                          false
% 11.10/2.01  --prep_def_merge                        true
% 11.10/2.01  --prep_def_merge_prop_impl              false
% 11.10/2.01  --prep_def_merge_mbd                    true
% 11.10/2.01  --prep_def_merge_tr_red                 false
% 11.10/2.01  --prep_def_merge_tr_cl                  false
% 11.10/2.01  --smt_preprocessing                     true
% 11.10/2.01  --smt_ac_axioms                         fast
% 11.10/2.01  --preprocessed_out                      false
% 11.10/2.01  --preprocessed_stats                    false
% 11.10/2.01  
% 11.10/2.01  ------ Abstraction refinement Options
% 11.10/2.01  
% 11.10/2.01  --abstr_ref                             []
% 11.10/2.01  --abstr_ref_prep                        false
% 11.10/2.01  --abstr_ref_until_sat                   false
% 11.10/2.01  --abstr_ref_sig_restrict                funpre
% 11.10/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.10/2.01  --abstr_ref_under                       []
% 11.10/2.01  
% 11.10/2.01  ------ SAT Options
% 11.10/2.01  
% 11.10/2.01  --sat_mode                              false
% 11.10/2.01  --sat_fm_restart_options                ""
% 11.10/2.01  --sat_gr_def                            false
% 11.10/2.01  --sat_epr_types                         true
% 11.10/2.01  --sat_non_cyclic_types                  false
% 11.10/2.01  --sat_finite_models                     false
% 11.10/2.01  --sat_fm_lemmas                         false
% 11.10/2.01  --sat_fm_prep                           false
% 11.10/2.01  --sat_fm_uc_incr                        true
% 11.10/2.01  --sat_out_model                         small
% 11.10/2.01  --sat_out_clauses                       false
% 11.10/2.01  
% 11.10/2.01  ------ QBF Options
% 11.10/2.01  
% 11.10/2.01  --qbf_mode                              false
% 11.10/2.01  --qbf_elim_univ                         false
% 11.10/2.01  --qbf_dom_inst                          none
% 11.10/2.01  --qbf_dom_pre_inst                      false
% 11.10/2.01  --qbf_sk_in                             false
% 11.10/2.01  --qbf_pred_elim                         true
% 11.10/2.01  --qbf_split                             512
% 11.10/2.01  
% 11.10/2.01  ------ BMC1 Options
% 11.10/2.01  
% 11.10/2.01  --bmc1_incremental                      false
% 11.10/2.01  --bmc1_axioms                           reachable_all
% 11.10/2.01  --bmc1_min_bound                        0
% 11.10/2.01  --bmc1_max_bound                        -1
% 11.10/2.01  --bmc1_max_bound_default                -1
% 11.10/2.01  --bmc1_symbol_reachability              true
% 11.10/2.01  --bmc1_property_lemmas                  false
% 11.10/2.01  --bmc1_k_induction                      false
% 11.10/2.01  --bmc1_non_equiv_states                 false
% 11.10/2.01  --bmc1_deadlock                         false
% 11.10/2.01  --bmc1_ucm                              false
% 11.10/2.01  --bmc1_add_unsat_core                   none
% 11.10/2.01  --bmc1_unsat_core_children              false
% 11.10/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.10/2.01  --bmc1_out_stat                         full
% 11.10/2.01  --bmc1_ground_init                      false
% 11.10/2.01  --bmc1_pre_inst_next_state              false
% 11.10/2.01  --bmc1_pre_inst_state                   false
% 11.10/2.01  --bmc1_pre_inst_reach_state             false
% 11.10/2.01  --bmc1_out_unsat_core                   false
% 11.10/2.01  --bmc1_aig_witness_out                  false
% 11.10/2.01  --bmc1_verbose                          false
% 11.10/2.01  --bmc1_dump_clauses_tptp                false
% 11.10/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.10/2.01  --bmc1_dump_file                        -
% 11.10/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.10/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.10/2.01  --bmc1_ucm_extend_mode                  1
% 11.10/2.01  --bmc1_ucm_init_mode                    2
% 11.10/2.01  --bmc1_ucm_cone_mode                    none
% 11.10/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.10/2.01  --bmc1_ucm_relax_model                  4
% 11.10/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.10/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.10/2.01  --bmc1_ucm_layered_model                none
% 11.10/2.01  --bmc1_ucm_max_lemma_size               10
% 11.10/2.01  
% 11.10/2.01  ------ AIG Options
% 11.10/2.01  
% 11.10/2.01  --aig_mode                              false
% 11.10/2.01  
% 11.10/2.01  ------ Instantiation Options
% 11.10/2.01  
% 11.10/2.01  --instantiation_flag                    true
% 11.10/2.01  --inst_sos_flag                         true
% 11.10/2.01  --inst_sos_phase                        true
% 11.10/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.10/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.10/2.01  --inst_lit_sel_side                     none
% 11.10/2.01  --inst_solver_per_active                1400
% 11.10/2.01  --inst_solver_calls_frac                1.
% 11.10/2.01  --inst_passive_queue_type               priority_queues
% 11.10/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.10/2.01  --inst_passive_queues_freq              [25;2]
% 11.10/2.01  --inst_dismatching                      true
% 11.10/2.01  --inst_eager_unprocessed_to_passive     true
% 11.10/2.01  --inst_prop_sim_given                   true
% 11.10/2.01  --inst_prop_sim_new                     false
% 11.10/2.01  --inst_subs_new                         false
% 11.10/2.01  --inst_eq_res_simp                      false
% 11.10/2.01  --inst_subs_given                       false
% 11.10/2.01  --inst_orphan_elimination               true
% 11.10/2.01  --inst_learning_loop_flag               true
% 11.10/2.01  --inst_learning_start                   3000
% 11.10/2.01  --inst_learning_factor                  2
% 11.10/2.01  --inst_start_prop_sim_after_learn       3
% 11.10/2.01  --inst_sel_renew                        solver
% 11.10/2.01  --inst_lit_activity_flag                true
% 11.10/2.01  --inst_restr_to_given                   false
% 11.10/2.01  --inst_activity_threshold               500
% 11.10/2.01  --inst_out_proof                        true
% 11.10/2.01  
% 11.10/2.01  ------ Resolution Options
% 11.10/2.01  
% 11.10/2.01  --resolution_flag                       false
% 11.10/2.01  --res_lit_sel                           adaptive
% 11.10/2.01  --res_lit_sel_side                      none
% 11.10/2.01  --res_ordering                          kbo
% 11.10/2.01  --res_to_prop_solver                    active
% 11.10/2.01  --res_prop_simpl_new                    false
% 11.10/2.01  --res_prop_simpl_given                  true
% 11.10/2.01  --res_passive_queue_type                priority_queues
% 11.10/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.10/2.01  --res_passive_queues_freq               [15;5]
% 11.10/2.01  --res_forward_subs                      full
% 11.10/2.01  --res_backward_subs                     full
% 11.10/2.01  --res_forward_subs_resolution           true
% 11.10/2.01  --res_backward_subs_resolution          true
% 11.10/2.01  --res_orphan_elimination                true
% 11.10/2.01  --res_time_limit                        2.
% 11.10/2.01  --res_out_proof                         true
% 11.10/2.01  
% 11.10/2.01  ------ Superposition Options
% 11.10/2.01  
% 11.10/2.01  --superposition_flag                    true
% 11.10/2.01  --sup_passive_queue_type                priority_queues
% 11.10/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.10/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.10/2.01  --demod_completeness_check              fast
% 11.10/2.01  --demod_use_ground                      true
% 11.10/2.01  --sup_to_prop_solver                    passive
% 11.10/2.01  --sup_prop_simpl_new                    true
% 11.10/2.01  --sup_prop_simpl_given                  true
% 11.10/2.01  --sup_fun_splitting                     true
% 11.10/2.01  --sup_smt_interval                      50000
% 11.10/2.01  
% 11.10/2.01  ------ Superposition Simplification Setup
% 11.10/2.01  
% 11.10/2.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.10/2.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.10/2.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.10/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.10/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.10/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.10/2.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.10/2.01  --sup_immed_triv                        [TrivRules]
% 11.10/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_immed_bw_main                     []
% 11.10/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.10/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.10/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.10/2.01  --sup_input_bw                          []
% 11.10/2.01  
% 11.10/2.01  ------ Combination Options
% 11.10/2.01  
% 11.10/2.01  --comb_res_mult                         3
% 11.10/2.01  --comb_sup_mult                         2
% 11.10/2.01  --comb_inst_mult                        10
% 11.10/2.01  
% 11.10/2.01  ------ Debug Options
% 11.10/2.01  
% 11.10/2.01  --dbg_backtrace                         false
% 11.10/2.01  --dbg_dump_prop_clauses                 false
% 11.10/2.01  --dbg_dump_prop_clauses_file            -
% 11.10/2.01  --dbg_out_stat                          false
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  ------ Proving...
% 11.10/2.01  
% 11.10/2.01  
% 11.10/2.01  % SZS status Theorem for theBenchmark.p
% 11.10/2.01  
% 11.10/2.01   Resolution empty clause
% 11.10/2.01  
% 11.10/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.10/2.01  
% 11.10/2.01  fof(f16,conjecture,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f17,negated_conjecture,(
% 11.10/2.01    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 11.10/2.01    inference(negated_conjecture,[],[f16])).
% 11.10/2.01  
% 11.10/2.01  fof(f32,plain,(
% 11.10/2.01    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f17])).
% 11.10/2.01  
% 11.10/2.01  fof(f33,plain,(
% 11.10/2.01    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 11.10/2.01    inference(flattening,[],[f32])).
% 11.10/2.01  
% 11.10/2.01  fof(f45,plain,(
% 11.10/2.01    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK3,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK3,X0))) )),
% 11.10/2.01    introduced(choice_axiom,[])).
% 11.10/2.01  
% 11.10/2.01  fof(f44,plain,(
% 11.10/2.01    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK2,X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK2,X0))) )),
% 11.10/2.01    introduced(choice_axiom,[])).
% 11.10/2.01  
% 11.10/2.01  fof(f43,plain,(
% 11.10/2.01    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK1) & v1_tex_2(X1,sK1) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK1)) & m1_pre_topc(X1,sK1)) & l1_pre_topc(sK1))),
% 11.10/2.01    introduced(choice_axiom,[])).
% 11.10/2.01  
% 11.10/2.01  fof(f46,plain,(
% 11.10/2.01    ((~v1_tex_2(sK3,sK1) & v1_tex_2(sK2,sK1) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK1)) & m1_pre_topc(sK2,sK1)) & l1_pre_topc(sK1)),
% 11.10/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f45,f44,f43])).
% 11.10/2.01  
% 11.10/2.01  fof(f72,plain,(
% 11.10/2.01    m1_pre_topc(sK2,sK1)),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f9,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f24,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f9])).
% 11.10/2.01  
% 11.10/2.01  fof(f59,plain,(
% 11.10/2.01    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f24])).
% 11.10/2.01  
% 11.10/2.01  fof(f71,plain,(
% 11.10/2.01    l1_pre_topc(sK1)),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f8,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f23,plain,(
% 11.10/2.01    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f8])).
% 11.10/2.01  
% 11.10/2.01  fof(f58,plain,(
% 11.10/2.01    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f23])).
% 11.10/2.01  
% 11.10/2.01  fof(f6,axiom,(
% 11.10/2.01    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f20,plain,(
% 11.10/2.01    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f6])).
% 11.10/2.01  
% 11.10/2.01  fof(f55,plain,(
% 11.10/2.01    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f20])).
% 11.10/2.01  
% 11.10/2.01  fof(f3,axiom,(
% 11.10/2.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f51,plain,(
% 11.10/2.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 11.10/2.01    inference(cnf_transformation,[],[f3])).
% 11.10/2.01  
% 11.10/2.01  fof(f2,axiom,(
% 11.10/2.01    ! [X0] : k2_subset_1(X0) = X0),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f50,plain,(
% 11.10/2.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.10/2.01    inference(cnf_transformation,[],[f2])).
% 11.10/2.01  
% 11.10/2.01  fof(f7,axiom,(
% 11.10/2.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f21,plain,(
% 11.10/2.01    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.10/2.01    inference(ennf_transformation,[],[f7])).
% 11.10/2.01  
% 11.10/2.01  fof(f22,plain,(
% 11.10/2.01    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(flattening,[],[f21])).
% 11.10/2.01  
% 11.10/2.01  fof(f57,plain,(
% 11.10/2.01    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f22])).
% 11.10/2.01  
% 11.10/2.01  fof(f11,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f26,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f11])).
% 11.10/2.01  
% 11.10/2.01  fof(f37,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(nnf_transformation,[],[f26])).
% 11.10/2.01  
% 11.10/2.01  fof(f61,plain,(
% 11.10/2.01    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f37])).
% 11.10/2.01  
% 11.10/2.01  fof(f73,plain,(
% 11.10/2.01    m1_pre_topc(sK3,sK1)),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f74,plain,(
% 11.10/2.01    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f10,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f25,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f10])).
% 11.10/2.01  
% 11.10/2.01  fof(f60,plain,(
% 11.10/2.01    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f25])).
% 11.10/2.01  
% 11.10/2.01  fof(f13,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f28,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f13])).
% 11.10/2.01  
% 11.10/2.01  fof(f64,plain,(
% 11.10/2.01    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f28])).
% 11.10/2.01  
% 11.10/2.01  fof(f1,axiom,(
% 11.10/2.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f34,plain,(
% 11.10/2.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.10/2.01    inference(nnf_transformation,[],[f1])).
% 11.10/2.01  
% 11.10/2.01  fof(f35,plain,(
% 11.10/2.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.10/2.01    inference(flattening,[],[f34])).
% 11.10/2.01  
% 11.10/2.01  fof(f49,plain,(
% 11.10/2.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f35])).
% 11.10/2.01  
% 11.10/2.01  fof(f5,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f18,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f5])).
% 11.10/2.01  
% 11.10/2.01  fof(f19,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(flattening,[],[f18])).
% 11.10/2.01  
% 11.10/2.01  fof(f36,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(nnf_transformation,[],[f19])).
% 11.10/2.01  
% 11.10/2.01  fof(f53,plain,(
% 11.10/2.01    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f36])).
% 11.10/2.01  
% 11.10/2.01  fof(f80,plain,(
% 11.10/2.01    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(equality_resolution,[],[f53])).
% 11.10/2.01  
% 11.10/2.01  fof(f56,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f22])).
% 11.10/2.01  
% 11.10/2.01  fof(f14,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f29,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f14])).
% 11.10/2.01  
% 11.10/2.01  fof(f30,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(flattening,[],[f29])).
% 11.10/2.01  
% 11.10/2.01  fof(f38,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(nnf_transformation,[],[f30])).
% 11.10/2.01  
% 11.10/2.01  fof(f39,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(rectify,[],[f38])).
% 11.10/2.01  
% 11.10/2.01  fof(f40,plain,(
% 11.10/2.01    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.10/2.01    introduced(choice_axiom,[])).
% 11.10/2.01  
% 11.10/2.01  fof(f41,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 11.10/2.01  
% 11.10/2.01  fof(f66,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f41])).
% 11.10/2.01  
% 11.10/2.01  fof(f76,plain,(
% 11.10/2.01    ~v1_tex_2(sK3,sK1)),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f67,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f41])).
% 11.10/2.01  
% 11.10/2.01  fof(f15,axiom,(
% 11.10/2.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f31,plain,(
% 11.10/2.01    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.10/2.01    inference(ennf_transformation,[],[f15])).
% 11.10/2.01  
% 11.10/2.01  fof(f42,plain,(
% 11.10/2.01    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.10/2.01    inference(nnf_transformation,[],[f31])).
% 11.10/2.01  
% 11.10/2.01  fof(f70,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.10/2.01    inference(cnf_transformation,[],[f42])).
% 11.10/2.01  
% 11.10/2.01  fof(f68,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f41])).
% 11.10/2.01  
% 11.10/2.01  fof(f65,plain,(
% 11.10/2.01    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f41])).
% 11.10/2.01  
% 11.10/2.01  fof(f81,plain,(
% 11.10/2.01    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(equality_resolution,[],[f65])).
% 11.10/2.01  
% 11.10/2.01  fof(f12,axiom,(
% 11.10/2.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f27,plain,(
% 11.10/2.01    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 11.10/2.01    inference(ennf_transformation,[],[f12])).
% 11.10/2.01  
% 11.10/2.01  fof(f63,plain,(
% 11.10/2.01    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f27])).
% 11.10/2.01  
% 11.10/2.01  fof(f75,plain,(
% 11.10/2.01    v1_tex_2(sK2,sK1)),
% 11.10/2.01    inference(cnf_transformation,[],[f46])).
% 11.10/2.01  
% 11.10/2.01  fof(f4,axiom,(
% 11.10/2.01    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 11.10/2.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.10/2.01  
% 11.10/2.01  fof(f52,plain,(
% 11.10/2.01    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 11.10/2.01    inference(cnf_transformation,[],[f4])).
% 11.10/2.01  
% 11.10/2.01  cnf(c_28,negated_conjecture,
% 11.10/2.01      ( m1_pre_topc(sK2,sK1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f72]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2374,plain,
% 11.10/2.01      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_12,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 11.10/2.01      inference(cnf_transformation,[],[f59]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2381,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3322,plain,
% 11.10/2.01      ( l1_pre_topc(sK2) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2374,c_2381]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_29,negated_conjecture,
% 11.10/2.01      ( l1_pre_topc(sK1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f71]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_30,plain,
% 11.10/2.01      ( l1_pre_topc(sK1) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3699,plain,
% 11.10/2.01      ( l1_pre_topc(sK2) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_3322,c_30]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_11,plain,
% 11.10/2.01      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 11.10/2.01      inference(cnf_transformation,[],[f58]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_8,plain,
% 11.10/2.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.10/2.01      inference(cnf_transformation,[],[f55]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_332,plain,
% 11.10/2.01      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.10/2.01      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2370,plain,
% 11.10/2.01      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3703,plain,
% 11.10/2.01      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3699,c_2370]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4,plain,
% 11.10/2.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 11.10/2.01      inference(cnf_transformation,[],[f51]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2386,plain,
% 11.10/2.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3,plain,
% 11.10/2.01      ( k2_subset_1(X0) = X0 ),
% 11.10/2.01      inference(cnf_transformation,[],[f50]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2390,plain,
% 11.10/2.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_2386,c_3]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_9,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.10/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.10/2.01      | ~ l1_pre_topc(X0) ),
% 11.10/2.01      inference(cnf_transformation,[],[f57]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2383,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 11.10/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4285,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)),X0) = iProver_top
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2390,c_2383]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6640,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK2) = iProver_top
% 11.10/2.01      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3703,c_4285]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7105,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK2) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_6640,c_30,c_3322]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_15,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X0)
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f61]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_175,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.10/2.01      | ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_15,c_12]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_176,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_175]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2372,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_176]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_5920,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.01      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3703,c_2372]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_27,negated_conjecture,
% 11.10/2.01      ( m1_pre_topc(sK3,sK1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f73]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2375,plain,
% 11.10/2.01      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3321,plain,
% 11.10/2.01      ( l1_pre_topc(sK1) != iProver_top | l1_pre_topc(sK3) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2375,c_2381]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3693,plain,
% 11.10/2.01      ( l1_pre_topc(sK3) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_3321,c_30]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3697,plain,
% 11.10/2.01      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3693,c_2370]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_26,negated_conjecture,
% 11.10/2.01      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 11.10/2.01      inference(cnf_transformation,[],[f74]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3788,plain,
% 11.10/2.01      ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 11.10/2.01      inference(demodulation,[status(thm)],[c_3697,c_26]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3789,plain,
% 11.10/2.01      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_3788,c_3703]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_5925,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.01      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_5920,c_3789]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6176,plain,
% 11.10/2.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_5925,c_30,c_3322]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6177,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK2) != iProver_top ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_6176]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_13,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f60]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2380,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4270,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK3) = iProver_top
% 11.10/2.01      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3697,c_2380]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_11573,plain,
% 11.10/2.01      ( m1_pre_topc(X0,sK3) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_4270,c_30,c_3321]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_11574,plain,
% 11.10/2.01      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK3) = iProver_top ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_11573]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_11579,plain,
% 11.10/2.01      ( m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK3) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_6177,c_11574]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_11592,plain,
% 11.10/2.01      ( m1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2)),sK3) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_7105,c_11579]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_17,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f64]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2378,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_0,plain,
% 11.10/2.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.10/2.01      inference(cnf_transformation,[],[f49]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2388,plain,
% 11.10/2.01      ( X0 = X1
% 11.10/2.01      | r1_tarski(X0,X1) != iProver_top
% 11.10/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3581,plain,
% 11.10/2.01      ( u1_struct_0(X0) = u1_struct_0(X1)
% 11.10/2.01      | m1_pre_topc(X1,X0) != iProver_top
% 11.10/2.01      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2378,c_2388]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7313,plain,
% 11.10/2.01      ( u1_struct_0(X0) = u1_struct_0(X1)
% 11.10/2.01      | m1_pre_topc(X1,X0) != iProver_top
% 11.10/2.01      | m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2378,c_3581]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_66,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_20295,plain,
% 11.10/2.01      ( m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | m1_pre_topc(X1,X0) != iProver_top
% 11.10/2.01      | u1_struct_0(X0) = u1_struct_0(X1)
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_7313,c_66]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_20296,plain,
% 11.10/2.01      ( u1_struct_0(X0) = u1_struct_0(X1)
% 11.10/2.01      | m1_pre_topc(X0,X1) != iProver_top
% 11.10/2.01      | m1_pre_topc(X1,X0) != iProver_top
% 11.10/2.01      | l1_pre_topc(X1) != iProver_top ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_20295]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_34835,plain,
% 11.10/2.01      ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = u1_struct_0(sK3)
% 11.10/2.01      | m1_pre_topc(sK3,k1_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top
% 11.10/2.01      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_11592,c_20296]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6643,plain,
% 11.10/2.01      ( l1_pre_topc(X0) != iProver_top
% 11.10/2.01      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_4285,c_2381]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6768,plain,
% 11.10/2.01      ( l1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top
% 11.10/2.01      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3703,c_6643]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7009,plain,
% 11.10/2.01      ( l1_pre_topc(k1_pre_topc(sK2,k2_struct_0(sK2))) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_6768,c_30,c_3322]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7014,plain,
% 11.10/2.01      ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_7009,c_2370]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7,plain,
% 11.10/2.01      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 11.10/2.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.10/2.01      | ~ l1_pre_topc(X0)
% 11.10/2.01      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.10/2.01      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.10/2.01      inference(cnf_transformation,[],[f80]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_191,plain,
% 11.10/2.01      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.10/2.01      | ~ l1_pre_topc(X0)
% 11.10/2.01      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 11.10/2.01      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_7,c_9]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_192,plain,
% 11.10/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 11.10/2.01      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_191]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_10,plain,
% 11.10/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 11.10/2.01      inference(cnf_transformation,[],[f56]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_197,plain,
% 11.10/2.01      ( ~ l1_pre_topc(X1)
% 11.10/2.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_192,c_10]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_198,plain,
% 11.10/2.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_197]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2371,plain,
% 11.10/2.01      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 11.10/2.01      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_198]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4896,plain,
% 11.10/2.01      ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 11.10/2.01      | l1_pre_topc(X0) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2390,c_2371]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6780,plain,
% 11.10/2.01      ( k2_struct_0(k1_pre_topc(sK2,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3699,c_4896]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6784,plain,
% 11.10/2.01      ( k2_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(sK2) ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_6780,c_3703]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_7015,plain,
% 11.10/2.01      ( u1_struct_0(k1_pre_topc(sK2,k2_struct_0(sK2))) = k2_struct_0(sK2) ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_7014,c_6784]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_34844,plain,
% 11.10/2.01      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 11.10/2.01      | m1_pre_topc(sK3,k1_pre_topc(sK2,k2_struct_0(sK2))) != iProver_top
% 11.10/2.01      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_34835,c_3697,c_7015]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2373,plain,
% 11.10/2.01      ( l1_pre_topc(sK1) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3075,plain,
% 11.10/2.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_2373,c_2370]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3580,plain,
% 11.10/2.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 11.10/2.01      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
% 11.10/2.01      | l1_pre_topc(sK1) != iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3075,c_2378]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4049,plain,
% 11.10/2.01      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
% 11.10/2.01      | m1_pre_topc(X0,sK1) != iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_3580,c_30]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4050,plain,
% 11.10/2.01      ( m1_pre_topc(X0,sK1) != iProver_top
% 11.10/2.01      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.01      inference(renaming,[status(thm)],[c_4049]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_4055,plain,
% 11.10/2.01      ( m1_pre_topc(sK2,sK1) != iProver_top
% 11.10/2.01      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3703,c_4050]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_31,plain,
% 11.10/2.01      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6434,plain,
% 11.10/2.01      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_4055,c_31]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_20,plain,
% 11.10/2.01      ( v1_tex_2(X0,X1)
% 11.10/2.01      | ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f66]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_24,negated_conjecture,
% 11.10/2.01      ( ~ v1_tex_2(sK3,sK1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f76]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_552,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | sK1 != X1
% 11.10/2.01      | sK3 != X0 ),
% 11.10/2.01      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_553,plain,
% 11.10/2.01      ( ~ m1_pre_topc(sK3,sK1)
% 11.10/2.01      | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 11.10/2.01      | ~ l1_pre_topc(sK1) ),
% 11.10/2.01      inference(unflattening,[status(thm)],[c_552]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_555,plain,
% 11.10/2.01      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_553,c_29,c_27]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2366,plain,
% 11.10/2.01      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_19,plain,
% 11.10/2.01      ( v1_tex_2(X0,X1)
% 11.10/2.01      | ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | sK0(X1,X0) = u1_struct_0(X0) ),
% 11.10/2.01      inference(cnf_transformation,[],[f67]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_563,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | sK0(X1,X0) = u1_struct_0(X0)
% 11.10/2.01      | sK1 != X1
% 11.10/2.01      | sK3 != X0 ),
% 11.10/2.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_564,plain,
% 11.10/2.01      ( ~ m1_pre_topc(sK3,sK1)
% 11.10/2.01      | ~ l1_pre_topc(sK1)
% 11.10/2.01      | sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 11.10/2.01      inference(unflattening,[status(thm)],[c_563]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_566,plain,
% 11.10/2.01      ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_564,c_29,c_27]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2392,plain,
% 11.10/2.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_2366,c_566]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3076,plain,
% 11.10/2.01      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 11.10/2.01      inference(demodulation,[status(thm)],[c_3075,c_2392]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_22,plain,
% 11.10/2.01      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 11.10/2.01      inference(cnf_transformation,[],[f70]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2377,plain,
% 11.10/2.01      ( X0 = X1
% 11.10/2.01      | v1_subset_1(X0,X1) = iProver_top
% 11.10/2.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3448,plain,
% 11.10/2.01      ( u1_struct_0(sK3) = k2_struct_0(sK1)
% 11.10/2.01      | v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.01      inference(superposition,[status(thm)],[c_3076,c_2377]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_18,plain,
% 11.10/2.01      ( v1_tex_2(X0,X1)
% 11.10/2.01      | ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 11.10/2.01      | ~ l1_pre_topc(X1) ),
% 11.10/2.01      inference(cnf_transformation,[],[f68]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_571,plain,
% 11.10/2.01      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.01      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 11.10/2.01      | ~ l1_pre_topc(X1)
% 11.10/2.01      | sK1 != X1
% 11.10/2.01      | sK3 != X0 ),
% 11.10/2.01      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_572,plain,
% 11.10/2.01      ( ~ m1_pre_topc(sK3,sK1)
% 11.10/2.01      | ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1))
% 11.10/2.01      | ~ l1_pre_topc(sK1) ),
% 11.10/2.01      inference(unflattening,[status(thm)],[c_571]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_574,plain,
% 11.10/2.01      ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) ),
% 11.10/2.01      inference(global_propositional_subsumption,
% 11.10/2.01                [status(thm)],
% 11.10/2.01                [c_572,c_29,c_27]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2365,plain,
% 11.10/2.01      ( v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
% 11.10/2.01      inference(predicate_to_equality,[status(thm)],[c_574]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_2391,plain,
% 11.10/2.01      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_2365,c_566]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_3077,plain,
% 11.10/2.01      ( v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
% 11.10/2.01      inference(demodulation,[status(thm)],[c_3075,c_2391]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_5356,plain,
% 11.10/2.01      ( u1_struct_0(sK3) = k2_struct_0(sK1) ),
% 11.10/2.01      inference(global_propositional_subsumption,[status(thm)],[c_3448,c_3077]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_5358,plain,
% 11.10/2.01      ( k2_struct_0(sK3) = k2_struct_0(sK1) ),
% 11.10/2.01      inference(light_normalisation,[status(thm)],[c_5356,c_3697]) ).
% 11.10/2.01  
% 11.10/2.01  cnf(c_6438,plain,
% 11.10/2.01      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_6434,c_5358]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_6440,plain,
% 11.10/2.02      ( k2_struct_0(sK2) = k2_struct_0(sK3)
% 11.10/2.02      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_6438,c_2388]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_6641,plain,
% 11.10/2.02      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top
% 11.10/2.02      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3697,c_4285]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_7180,plain,
% 11.10/2.02      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_6641,c_30,c_3321]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_5921,plain,
% 11.10/2.02      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK3) != iProver_top
% 11.10/2.02      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3697,c_2372]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_12070,plain,
% 11.10/2.02      ( m1_pre_topc(X0,sK3) != iProver_top
% 11.10/2.02      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_5921,c_30,c_3321]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_12071,plain,
% 11.10/2.02      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK3) != iProver_top ),
% 11.10/2.02      inference(renaming,[status(thm)],[c_12070]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_4269,plain,
% 11.10/2.02      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK2) = iProver_top
% 11.10/2.02      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3703,c_2380]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_4272,plain,
% 11.10/2.02      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK2) = iProver_top
% 11.10/2.02      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_4269,c_3789]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_4663,plain,
% 11.10/2.02      ( m1_pre_topc(X0,sK2) = iProver_top
% 11.10/2.02      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_4272,c_30,c_3322]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_4664,plain,
% 11.10/2.02      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK2) = iProver_top ),
% 11.10/2.02      inference(renaming,[status(thm)],[c_4663]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_12079,plain,
% 11.10/2.02      ( m1_pre_topc(X0,sK2) = iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK3) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_12071,c_4664]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_12087,plain,
% 11.10/2.02      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) = iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_7180,c_12079]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_6769,plain,
% 11.10/2.02      ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top
% 11.10/2.02      | l1_pre_topc(sK3) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3697,c_6643]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_7096,plain,
% 11.10/2.02      ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_6769,c_30,c_3321]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_7101,plain,
% 11.10/2.02      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_7096,c_2370]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_6779,plain,
% 11.10/2.02      ( k2_struct_0(k1_pre_topc(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3693,c_4896]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_6785,plain,
% 11.10/2.02      ( k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_6779,c_3697]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_7102,plain,
% 11.10/2.02      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_7101,c_6785]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_3919,plain,
% 11.10/2.02      ( m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.02      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 11.10/2.02      | l1_pre_topc(sK2) != iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_3703,c_2378]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_8399,plain,
% 11.10/2.02      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 11.10/2.02      | m1_pre_topc(X0,sK2) != iProver_top ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_3919,c_30,c_3322]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_8400,plain,
% 11.10/2.02      ( m1_pre_topc(X0,sK2) != iProver_top
% 11.10/2.02      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 11.10/2.02      inference(renaming,[status(thm)],[c_8399]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_33550,plain,
% 11.10/2.02      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
% 11.10/2.02      | r1_tarski(k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_7102,c_8400]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_35381,plain,
% 11.10/2.02      ( k2_struct_0(sK2) = k2_struct_0(sK3) ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_34844,c_6440,c_12087,c_33550]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_21,plain,
% 11.10/2.02      ( ~ v1_tex_2(X0,X1)
% 11.10/2.02      | ~ m1_pre_topc(X0,X1)
% 11.10/2.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.10/2.02      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.02      | ~ l1_pre_topc(X1) ),
% 11.10/2.02      inference(cnf_transformation,[],[f81]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_16,plain,
% 11.10/2.02      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.02      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.10/2.02      | ~ l1_pre_topc(X1) ),
% 11.10/2.02      inference(cnf_transformation,[],[f63]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_163,plain,
% 11.10/2.02      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.10/2.02      | ~ m1_pre_topc(X0,X1)
% 11.10/2.02      | ~ v1_tex_2(X0,X1)
% 11.10/2.02      | ~ l1_pre_topc(X1) ),
% 11.10/2.02      inference(global_propositional_subsumption,[status(thm)],[c_21,c_16]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_164,plain,
% 11.10/2.02      ( ~ v1_tex_2(X0,X1)
% 11.10/2.02      | ~ m1_pre_topc(X0,X1)
% 11.10/2.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.10/2.02      | ~ l1_pre_topc(X1) ),
% 11.10/2.02      inference(renaming,[status(thm)],[c_163]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_25,negated_conjecture,
% 11.10/2.02      ( v1_tex_2(sK2,sK1) ),
% 11.10/2.02      inference(cnf_transformation,[],[f75]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_582,plain,
% 11.10/2.02      ( ~ m1_pre_topc(X0,X1)
% 11.10/2.02      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 11.10/2.02      | ~ l1_pre_topc(X1)
% 11.10/2.02      | sK2 != X0
% 11.10/2.02      | sK1 != X1 ),
% 11.10/2.02      inference(resolution_lifted,[status(thm)],[c_164,c_25]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_583,plain,
% 11.10/2.02      ( ~ m1_pre_topc(sK2,sK1)
% 11.10/2.02      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 11.10/2.02      | ~ l1_pre_topc(sK1) ),
% 11.10/2.02      inference(unflattening,[status(thm)],[c_582]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_585,plain,
% 11.10/2.02      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 11.10/2.02      inference(global_propositional_subsumption,
% 11.10/2.02                [status(thm)],
% 11.10/2.02                [c_583,c_29,c_28]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_2364,plain,
% 11.10/2.02      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 11.10/2.02      inference(predicate_to_equality,[status(thm)],[c_585]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_3078,plain,
% 11.10/2.02      ( v1_subset_1(u1_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.02      inference(demodulation,[status(thm)],[c_3075,c_2364]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_3913,plain,
% 11.10/2.02      ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 11.10/2.02      inference(demodulation,[status(thm)],[c_3703,c_3078]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_5800,plain,
% 11.10/2.02      ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_3913,c_5358]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_35465,plain,
% 11.10/2.02      ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
% 11.10/2.02      inference(demodulation,[status(thm)],[c_35381,c_5800]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_5,plain,
% 11.10/2.02      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 11.10/2.02      inference(cnf_transformation,[],[f52]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_2385,plain,
% 11.10/2.02      ( v1_subset_1(k2_subset_1(X0),X0) != iProver_top ),
% 11.10/2.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_2389,plain,
% 11.10/2.02      ( v1_subset_1(X0,X0) != iProver_top ),
% 11.10/2.02      inference(light_normalisation,[status(thm)],[c_2385,c_3]) ).
% 11.10/2.02  
% 11.10/2.02  cnf(c_36857,plain,
% 11.10/2.02      ( $false ),
% 11.10/2.02      inference(superposition,[status(thm)],[c_35465,c_2389]) ).
% 11.10/2.02  
% 11.10/2.02  
% 11.10/2.02  % SZS output end CNFRefutation for theBenchmark.p
% 11.10/2.02  
% 11.10/2.02  ------                               Statistics
% 11.10/2.02  
% 11.10/2.02  ------ General
% 11.10/2.02  
% 11.10/2.02  abstr_ref_over_cycles:                  0
% 11.10/2.02  abstr_ref_under_cycles:                 0
% 11.10/2.02  gc_basic_clause_elim:                   0
% 11.10/2.02  forced_gc_time:                         0
% 11.10/2.02  parsing_time:                           0.026
% 11.10/2.02  unif_index_cands_time:                  0.
% 11.10/2.02  unif_index_add_time:                    0.
% 11.10/2.02  orderings_time:                         0.
% 11.10/2.02  out_proof_time:                         0.017
% 11.10/2.02  total_time:                             1.114
% 11.10/2.02  num_of_symbols:                         50
% 11.10/2.02  num_of_terms:                           21912
% 11.10/2.02  
% 11.10/2.02  ------ Preprocessing
% 11.10/2.02  
% 11.10/2.02  num_of_splits:                          0
% 11.10/2.02  num_of_split_atoms:                     0
% 11.10/2.02  num_of_reused_defs:                     0
% 11.10/2.02  num_eq_ax_congr_red:                    9
% 11.10/2.02  num_of_sem_filtered_clauses:            1
% 11.10/2.02  num_of_subtypes:                        0
% 11.10/2.02  monotx_restored_types:                  0
% 11.10/2.02  sat_num_of_epr_types:                   0
% 11.10/2.02  sat_num_of_non_cyclic_types:            0
% 11.10/2.02  sat_guarded_non_collapsed_types:        0
% 11.10/2.02  num_pure_diseq_elim:                    0
% 11.10/2.02  simp_replaced_by:                       0
% 11.10/2.02  res_preprocessed:                       146
% 11.10/2.02  prep_upred:                             0
% 11.10/2.02  prep_unflattend:                        58
% 11.10/2.02  smt_new_axioms:                         0
% 11.10/2.02  pred_elim_cands:                        6
% 11.10/2.02  pred_elim:                              2
% 11.10/2.02  pred_elim_cl:                           -1
% 11.10/2.02  pred_elim_cycles:                       7
% 11.10/2.02  merged_defs:                            0
% 11.10/2.02  merged_defs_ncl:                        0
% 11.10/2.02  bin_hyper_res:                          0
% 11.10/2.02  prep_cycles:                            4
% 11.10/2.02  pred_elim_time:                         0.042
% 11.10/2.02  splitting_time:                         0.
% 11.10/2.02  sem_filter_time:                        0.
% 11.10/2.02  monotx_time:                            0.
% 11.10/2.02  subtype_inf_time:                       0.
% 11.10/2.02  
% 11.10/2.02  ------ Problem properties
% 11.10/2.02  
% 11.10/2.02  clauses:                                29
% 11.10/2.02  conjectures:                            4
% 11.10/2.02  epr:                                    7
% 11.10/2.02  horn:                                   26
% 11.10/2.02  ground:                                 9
% 11.10/2.02  unary:                                  13
% 11.10/2.02  binary:                                 2
% 11.10/2.02  lits:                                   64
% 11.10/2.02  lits_eq:                                10
% 11.10/2.02  fd_pure:                                0
% 11.10/2.02  fd_pseudo:                              0
% 11.10/2.02  fd_cond:                                0
% 11.10/2.02  fd_pseudo_cond:                         2
% 11.10/2.02  ac_symbols:                             0
% 11.10/2.02  
% 11.10/2.02  ------ Propositional Solver
% 11.10/2.02  
% 11.10/2.02  prop_solver_calls:                      34
% 11.10/2.02  prop_fast_solver_calls:                 2386
% 11.10/2.02  smt_solver_calls:                       0
% 11.10/2.02  smt_fast_solver_calls:                  0
% 11.10/2.02  prop_num_of_clauses:                    13323
% 11.10/2.02  prop_preprocess_simplified:             32926
% 11.10/2.02  prop_fo_subsumed:                       125
% 11.10/2.02  prop_solver_time:                       0.
% 11.10/2.02  smt_solver_time:                        0.
% 11.10/2.02  smt_fast_solver_time:                   0.
% 11.10/2.02  prop_fast_solver_time:                  0.
% 11.10/2.02  prop_unsat_core_time:                   0.
% 11.10/2.02  
% 11.10/2.02  ------ QBF
% 11.10/2.02  
% 11.10/2.02  qbf_q_res:                              0
% 11.10/2.02  qbf_num_tautologies:                    0
% 11.10/2.02  qbf_prep_cycles:                        0
% 11.10/2.02  
% 11.10/2.02  ------ BMC1
% 11.10/2.02  
% 11.10/2.02  bmc1_current_bound:                     -1
% 11.10/2.02  bmc1_last_solved_bound:                 -1
% 11.10/2.02  bmc1_unsat_core_size:                   -1
% 11.10/2.02  bmc1_unsat_core_parents_size:           -1
% 11.10/2.02  bmc1_merge_next_fun:                    0
% 11.10/2.02  bmc1_unsat_core_clauses_time:           0.
% 11.10/2.02  
% 11.10/2.02  ------ Instantiation
% 11.10/2.02  
% 11.10/2.02  inst_num_of_clauses:                    4203
% 11.10/2.02  inst_num_in_passive:                    2482
% 11.10/2.02  inst_num_in_active:                     1284
% 11.10/2.02  inst_num_in_unprocessed:                437
% 11.10/2.02  inst_num_of_loops:                      1590
% 11.10/2.02  inst_num_of_learning_restarts:          0
% 11.10/2.02  inst_num_moves_active_passive:          303
% 11.10/2.02  inst_lit_activity:                      0
% 11.10/2.02  inst_lit_activity_moves:                1
% 11.10/2.02  inst_num_tautologies:                   0
% 11.10/2.02  inst_num_prop_implied:                  0
% 11.10/2.02  inst_num_existing_simplified:           0
% 11.10/2.02  inst_num_eq_res_simplified:             0
% 11.10/2.02  inst_num_child_elim:                    0
% 11.10/2.02  inst_num_of_dismatching_blockings:      3395
% 11.10/2.02  inst_num_of_non_proper_insts:           5610
% 11.10/2.02  inst_num_of_duplicates:                 0
% 11.10/2.02  inst_inst_num_from_inst_to_res:         0
% 11.10/2.02  inst_dismatching_checking_time:         0.
% 11.10/2.02  
% 11.10/2.02  ------ Resolution
% 11.10/2.02  
% 11.10/2.02  res_num_of_clauses:                     0
% 11.10/2.02  res_num_in_passive:                     0
% 11.10/2.02  res_num_in_active:                      0
% 11.10/2.02  res_num_of_loops:                       150
% 11.10/2.02  res_forward_subset_subsumed:            815
% 11.10/2.02  res_backward_subset_subsumed:           2
% 11.10/2.02  res_forward_subsumed:                   0
% 11.10/2.02  res_backward_subsumed:                  0
% 11.10/2.02  res_forward_subsumption_resolution:     0
% 11.10/2.02  res_backward_subsumption_resolution:    0
% 11.10/2.02  res_clause_to_clause_subsumption:       4545
% 11.10/2.02  res_orphan_elimination:                 0
% 11.10/2.02  res_tautology_del:                      464
% 11.10/2.02  res_num_eq_res_simplified:              0
% 11.10/2.02  res_num_sel_changes:                    0
% 11.10/2.02  res_moves_from_active_to_pass:          0
% 11.10/2.02  
% 11.10/2.02  ------ Superposition
% 11.10/2.02  
% 11.10/2.02  sup_time_total:                         0.
% 11.10/2.02  sup_time_generating:                    0.
% 11.10/2.02  sup_time_sim_full:                      0.
% 11.10/2.02  sup_time_sim_immed:                     0.
% 11.10/2.02  
% 11.10/2.02  sup_num_of_clauses:                     875
% 11.10/2.02  sup_num_in_active:                      202
% 11.10/2.02  sup_num_in_passive:                     673
% 11.10/2.02  sup_num_of_loops:                       317
% 11.10/2.02  sup_fw_superposition:                   770
% 11.10/2.02  sup_bw_superposition:                   957
% 11.10/2.02  sup_immediate_simplified:               852
% 11.10/2.02  sup_given_eliminated:                   1
% 11.10/2.02  comparisons_done:                       0
% 11.10/2.02  comparisons_avoided:                    0
% 11.10/2.02  
% 11.10/2.02  ------ Simplifications
% 11.10/2.02  
% 11.10/2.02  
% 11.10/2.02  sim_fw_subset_subsumed:                 260
% 11.10/2.02  sim_bw_subset_subsumed:                 58
% 11.10/2.02  sim_fw_subsumed:                        167
% 11.10/2.02  sim_bw_subsumed:                        11
% 11.10/2.02  sim_fw_subsumption_res:                 0
% 11.10/2.02  sim_bw_subsumption_res:                 0
% 11.10/2.02  sim_tautology_del:                      7
% 11.10/2.02  sim_eq_tautology_del:                   47
% 11.10/2.02  sim_eq_res_simp:                        0
% 11.10/2.02  sim_fw_demodulated:                     13
% 11.10/2.02  sim_bw_demodulated:                     106
% 11.10/2.02  sim_light_normalised:                   502
% 11.10/2.02  sim_joinable_taut:                      0
% 11.10/2.02  sim_joinable_simp:                      0
% 11.10/2.02  sim_ac_normalised:                      0
% 11.10/2.02  sim_smt_subsumption:                    0
% 11.10/2.02  
%------------------------------------------------------------------------------
