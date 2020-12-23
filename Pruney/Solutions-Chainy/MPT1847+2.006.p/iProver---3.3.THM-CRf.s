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
% DateTime   : Thu Dec  3 12:25:24 EST 2020

% Result     : Theorem 19.19s
% Output     : CNFRefutation 19.19s
% Verified   : 
% Statistics : Number of formulae       :  226 (4333 expanded)
%              Number of clauses        :  151 (1322 expanded)
%              Number of leaves         :   18 (1189 expanded)
%              Depth                    :   26
%              Number of atoms          :  645 (19807 expanded)
%              Number of equality atoms :  267 (4441 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( ( v1_tex_2(X1,X0)
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
               => v1_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f44,plain,(
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

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( ~ v1_tex_2(sK3,sK1)
    & v1_tex_2(sK2,sK1)
    & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    & m1_pre_topc(sK3,sK1)
    & m1_pre_topc(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f44,f43,f42])).

fof(f69,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f71,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f67])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2570,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_383,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_10,c_7])).

cnf(c_2566,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_383])).

cnf(c_3371,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_2570,c_2566])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2572,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2577,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3796,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2572,c_2577])).

cnf(c_29,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3978,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3796,c_29])).

cnf(c_3982,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3978,c_2566])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2574,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4084,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3982,c_2574])).

cnf(c_8044,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4084,c_29,c_3796])).

cnf(c_8045,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_8044])).

cnf(c_8052,plain,
    ( m1_pre_topc(sK1,sK3) != iProver_top
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_8045])).

cnf(c_19,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_23,negated_conjecture,
    ( ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_579,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_580,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_28,c_26])).

cnf(c_2561,plain,
    ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_18,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_590,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_591,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_593,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_591,c_28,c_26])).

cnf(c_2585,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2561,c_593])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3202,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2585,c_2581])).

cnf(c_3469,plain,
    ( r1_tarski(u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3371,c_3202])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2584,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3802,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK1)
    | r1_tarski(k2_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3469,c_2584])).

cnf(c_5358,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3802,c_3982])).

cnf(c_8213,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK1)
    | m1_pre_topc(sK1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8052,c_5358])).

cnf(c_17,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_568,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_569,plain,
    ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_571,plain,
    ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_28,c_26])).

cnf(c_2562,plain,
    ( v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_2586,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2562,c_593])).

cnf(c_3470,plain,
    ( v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3371,c_2586])).

cnf(c_4071,plain,
    ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3982,c_3470])).

cnf(c_4072,plain,
    ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3982,c_3469])).

cnf(c_21,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_240,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_241,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_240])).

cnf(c_288,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_21,c_241])).

cnf(c_2567,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_7522,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK1)
    | v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4072,c_2567])).

cnf(c_8404,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8213,c_4071,c_7522])).

cnf(c_3471,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3371,c_2585])).

cnf(c_4070,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3982,c_3471])).

cnf(c_8414,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8404,c_4070])).

cnf(c_8,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2579,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4555,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3982,c_2579])).

cnf(c_15803,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_29,c_3796])).

cnf(c_15804,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_15803])).

cnf(c_55811,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_8414,c_15804])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_173,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_11])).

cnf(c_174,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_2569,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_6178,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3982,c_2569])).

cnf(c_17247,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6178,c_29,c_3796])).

cnf(c_17248,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_17247])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2571,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3797,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2571,c_2577])).

cnf(c_3984,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3797,c_29])).

cnf(c_3988,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_3984,c_2566])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2576,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4537,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3988,c_2576])).

cnf(c_25,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4074,plain,
    ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(demodulation,[status(thm)],[c_3982,c_25])).

cnf(c_4075,plain,
    ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_4074,c_3988])).

cnf(c_4540,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4537,c_4075])).

cnf(c_5077,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4540,c_29,c_3797])).

cnf(c_5078,plain,
    ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5077])).

cnf(c_17254,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_17248,c_5078])).

cnf(c_59456,plain,
    ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_55811,c_17254])).

cnf(c_3867,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_2584])).

cnf(c_7113,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2574,c_3867])).

cnf(c_65,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_22187,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7113,c_65])).

cnf(c_22188,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_22187])).

cnf(c_60959,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = u1_struct_0(sK2)
    | m1_pre_topc(sK2,k1_pre_topc(sK3,k2_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_59456,c_22188])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2583,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2582,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4551,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_2579])).

cnf(c_12539,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4551,c_2577])).

cnf(c_13406,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_12539])).

cnf(c_13428,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3982,c_13406])).

cnf(c_13688,plain,
    ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13428,c_29,c_3796])).

cnf(c_13693,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) ),
    inference(superposition,[status(thm)],[c_13688,c_2566])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_189,plain,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(k1_pre_topc(X0,X1))
    | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_8])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(k1_pre_topc(X1,X0))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_189])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_195,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_190,c_9])).

cnf(c_196,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(renaming,[status(thm)],[c_195])).

cnf(c_2568,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_196])).

cnf(c_5209,plain,
    ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_2568])).

cnf(c_10729,plain,
    ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2583,c_5209])).

cnf(c_10748,plain,
    ( k2_struct_0(k1_pre_topc(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(superposition,[status(thm)],[c_3978,c_10729])).

cnf(c_10755,plain,
    ( k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_10748,c_3982])).

cnf(c_13694,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_13693,c_10755])).

cnf(c_60968,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2)
    | m1_pre_topc(sK2,k1_pre_topc(sK3,k2_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_60959,c_3988,c_13694])).

cnf(c_3866,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3371,c_2574])).

cnf(c_4326,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3866,c_29])).

cnf(c_4327,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4326])).

cnf(c_4332,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3988,c_4327])).

cnf(c_30,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6930,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4332,c_30])).

cnf(c_8412,plain,
    ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8404,c_6930])).

cnf(c_4209,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3988,c_2574])).

cnf(c_9512,plain,
    ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4209,c_29,c_3797])).

cnf(c_9513,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_9512])).

cnf(c_9522,plain,
    ( u1_struct_0(X0) = k2_struct_0(sK2)
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9513,c_2584])).

cnf(c_58386,plain,
    ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK2)
    | m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13694,c_9522])).

cnf(c_58483,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2)
    | m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
    | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_58386,c_13694])).

cnf(c_61242,plain,
    ( k2_struct_0(sK3) = k2_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60968,c_8412,c_58483,c_59456])).

cnf(c_20,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_161,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_15])).

cnf(c_162,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_161])).

cnf(c_24,negated_conjecture,
    ( v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_598,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_162,c_24])).

cnf(c_599,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_598])).

cnf(c_601,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_599,c_28,c_27])).

cnf(c_2560,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_3472,plain,
    ( v1_subset_1(u1_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3371,c_2560])).

cnf(c_4202,plain,
    ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3988,c_3472])).

cnf(c_8415,plain,
    ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8404,c_4202])).

cnf(c_61260,plain,
    ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_61242,c_8415])).

cnf(c_22,plain,
    ( ~ v1_subset_1(X0,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2573,plain,
    ( v1_subset_1(X0,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3285,plain,
    ( v1_subset_1(X0,X0) != iProver_top
    | r1_tarski(X0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2582,c_2573])).

cnf(c_90,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5238,plain,
    ( v1_subset_1(X0,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3285,c_90])).

cnf(c_62478,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_61260,c_5238])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.19/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.19/2.99  
% 19.19/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.19/2.99  
% 19.19/2.99  ------  iProver source info
% 19.19/2.99  
% 19.19/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.19/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.19/2.99  git: non_committed_changes: false
% 19.19/2.99  git: last_make_outside_of_git: false
% 19.19/2.99  
% 19.19/2.99  ------ 
% 19.19/2.99  
% 19.19/2.99  ------ Input Options
% 19.19/2.99  
% 19.19/2.99  --out_options                           all
% 19.19/2.99  --tptp_safe_out                         true
% 19.19/2.99  --problem_path                          ""
% 19.19/2.99  --include_path                          ""
% 19.19/2.99  --clausifier                            res/vclausify_rel
% 19.19/2.99  --clausifier_options                    ""
% 19.19/2.99  --stdin                                 false
% 19.19/2.99  --stats_out                             all
% 19.19/2.99  
% 19.19/2.99  ------ General Options
% 19.19/2.99  
% 19.19/2.99  --fof                                   false
% 19.19/2.99  --time_out_real                         305.
% 19.19/2.99  --time_out_virtual                      -1.
% 19.19/2.99  --symbol_type_check                     false
% 19.19/2.99  --clausify_out                          false
% 19.19/2.99  --sig_cnt_out                           false
% 19.19/2.99  --trig_cnt_out                          false
% 19.19/2.99  --trig_cnt_out_tolerance                1.
% 19.19/2.99  --trig_cnt_out_sk_spl                   false
% 19.19/2.99  --abstr_cl_out                          false
% 19.19/2.99  
% 19.19/2.99  ------ Global Options
% 19.19/2.99  
% 19.19/2.99  --schedule                              default
% 19.19/2.99  --add_important_lit                     false
% 19.19/2.99  --prop_solver_per_cl                    1000
% 19.19/2.99  --min_unsat_core                        false
% 19.19/2.99  --soft_assumptions                      false
% 19.19/2.99  --soft_lemma_size                       3
% 19.19/2.99  --prop_impl_unit_size                   0
% 19.19/2.99  --prop_impl_unit                        []
% 19.19/2.99  --share_sel_clauses                     true
% 19.19/2.99  --reset_solvers                         false
% 19.19/2.99  --bc_imp_inh                            [conj_cone]
% 19.19/2.99  --conj_cone_tolerance                   3.
% 19.19/2.99  --extra_neg_conj                        none
% 19.19/2.99  --large_theory_mode                     true
% 19.19/2.99  --prolific_symb_bound                   200
% 19.19/2.99  --lt_threshold                          2000
% 19.19/2.99  --clause_weak_htbl                      true
% 19.19/2.99  --gc_record_bc_elim                     false
% 19.19/2.99  
% 19.19/2.99  ------ Preprocessing Options
% 19.19/2.99  
% 19.19/2.99  --preprocessing_flag                    true
% 19.19/2.99  --time_out_prep_mult                    0.1
% 19.19/2.99  --splitting_mode                        input
% 19.19/2.99  --splitting_grd                         true
% 19.19/2.99  --splitting_cvd                         false
% 19.19/2.99  --splitting_cvd_svl                     false
% 19.19/2.99  --splitting_nvd                         32
% 19.19/2.99  --sub_typing                            true
% 19.19/2.99  --prep_gs_sim                           true
% 19.19/2.99  --prep_unflatten                        true
% 19.19/2.99  --prep_res_sim                          true
% 19.19/2.99  --prep_upred                            true
% 19.19/2.99  --prep_sem_filter                       exhaustive
% 19.19/2.99  --prep_sem_filter_out                   false
% 19.19/2.99  --pred_elim                             true
% 19.19/2.99  --res_sim_input                         true
% 19.19/2.99  --eq_ax_congr_red                       true
% 19.19/2.99  --pure_diseq_elim                       true
% 19.19/2.99  --brand_transform                       false
% 19.19/2.99  --non_eq_to_eq                          false
% 19.19/2.99  --prep_def_merge                        true
% 19.19/2.99  --prep_def_merge_prop_impl              false
% 19.19/2.99  --prep_def_merge_mbd                    true
% 19.19/2.99  --prep_def_merge_tr_red                 false
% 19.19/2.99  --prep_def_merge_tr_cl                  false
% 19.19/2.99  --smt_preprocessing                     true
% 19.19/2.99  --smt_ac_axioms                         fast
% 19.19/2.99  --preprocessed_out                      false
% 19.19/2.99  --preprocessed_stats                    false
% 19.19/2.99  
% 19.19/2.99  ------ Abstraction refinement Options
% 19.19/2.99  
% 19.19/2.99  --abstr_ref                             []
% 19.19/2.99  --abstr_ref_prep                        false
% 19.19/2.99  --abstr_ref_until_sat                   false
% 19.19/2.99  --abstr_ref_sig_restrict                funpre
% 19.19/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.19/2.99  --abstr_ref_under                       []
% 19.19/2.99  
% 19.19/2.99  ------ SAT Options
% 19.19/2.99  
% 19.19/2.99  --sat_mode                              false
% 19.19/2.99  --sat_fm_restart_options                ""
% 19.19/2.99  --sat_gr_def                            false
% 19.19/2.99  --sat_epr_types                         true
% 19.19/2.99  --sat_non_cyclic_types                  false
% 19.19/2.99  --sat_finite_models                     false
% 19.19/2.99  --sat_fm_lemmas                         false
% 19.19/2.99  --sat_fm_prep                           false
% 19.19/2.99  --sat_fm_uc_incr                        true
% 19.19/2.99  --sat_out_model                         small
% 19.19/2.99  --sat_out_clauses                       false
% 19.19/2.99  
% 19.19/2.99  ------ QBF Options
% 19.19/2.99  
% 19.19/2.99  --qbf_mode                              false
% 19.19/2.99  --qbf_elim_univ                         false
% 19.19/2.99  --qbf_dom_inst                          none
% 19.19/2.99  --qbf_dom_pre_inst                      false
% 19.19/2.99  --qbf_sk_in                             false
% 19.19/2.99  --qbf_pred_elim                         true
% 19.19/2.99  --qbf_split                             512
% 19.19/2.99  
% 19.19/2.99  ------ BMC1 Options
% 19.19/2.99  
% 19.19/2.99  --bmc1_incremental                      false
% 19.19/2.99  --bmc1_axioms                           reachable_all
% 19.19/2.99  --bmc1_min_bound                        0
% 19.19/2.99  --bmc1_max_bound                        -1
% 19.19/2.99  --bmc1_max_bound_default                -1
% 19.19/2.99  --bmc1_symbol_reachability              true
% 19.19/2.99  --bmc1_property_lemmas                  false
% 19.19/2.99  --bmc1_k_induction                      false
% 19.19/2.99  --bmc1_non_equiv_states                 false
% 19.19/2.99  --bmc1_deadlock                         false
% 19.19/2.99  --bmc1_ucm                              false
% 19.19/2.99  --bmc1_add_unsat_core                   none
% 19.19/2.99  --bmc1_unsat_core_children              false
% 19.19/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.19/2.99  --bmc1_out_stat                         full
% 19.19/2.99  --bmc1_ground_init                      false
% 19.19/2.99  --bmc1_pre_inst_next_state              false
% 19.19/2.99  --bmc1_pre_inst_state                   false
% 19.19/2.99  --bmc1_pre_inst_reach_state             false
% 19.19/2.99  --bmc1_out_unsat_core                   false
% 19.19/2.99  --bmc1_aig_witness_out                  false
% 19.19/2.99  --bmc1_verbose                          false
% 19.19/2.99  --bmc1_dump_clauses_tptp                false
% 19.19/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.19/2.99  --bmc1_dump_file                        -
% 19.19/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.19/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.19/2.99  --bmc1_ucm_extend_mode                  1
% 19.19/2.99  --bmc1_ucm_init_mode                    2
% 19.19/2.99  --bmc1_ucm_cone_mode                    none
% 19.19/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.19/2.99  --bmc1_ucm_relax_model                  4
% 19.19/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.19/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.19/2.99  --bmc1_ucm_layered_model                none
% 19.19/2.99  --bmc1_ucm_max_lemma_size               10
% 19.19/2.99  
% 19.19/2.99  ------ AIG Options
% 19.19/2.99  
% 19.19/2.99  --aig_mode                              false
% 19.19/2.99  
% 19.19/2.99  ------ Instantiation Options
% 19.19/2.99  
% 19.19/2.99  --instantiation_flag                    true
% 19.19/2.99  --inst_sos_flag                         true
% 19.19/2.99  --inst_sos_phase                        true
% 19.19/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.19/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.19/2.99  --inst_lit_sel_side                     num_symb
% 19.19/2.99  --inst_solver_per_active                1400
% 19.19/2.99  --inst_solver_calls_frac                1.
% 19.19/2.99  --inst_passive_queue_type               priority_queues
% 19.19/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.19/2.99  --inst_passive_queues_freq              [25;2]
% 19.19/2.99  --inst_dismatching                      true
% 19.19/2.99  --inst_eager_unprocessed_to_passive     true
% 19.19/2.99  --inst_prop_sim_given                   true
% 19.19/2.99  --inst_prop_sim_new                     false
% 19.19/2.99  --inst_subs_new                         false
% 19.19/2.99  --inst_eq_res_simp                      false
% 19.19/2.99  --inst_subs_given                       false
% 19.19/2.99  --inst_orphan_elimination               true
% 19.19/2.99  --inst_learning_loop_flag               true
% 19.19/2.99  --inst_learning_start                   3000
% 19.19/2.99  --inst_learning_factor                  2
% 19.19/2.99  --inst_start_prop_sim_after_learn       3
% 19.19/2.99  --inst_sel_renew                        solver
% 19.19/2.99  --inst_lit_activity_flag                true
% 19.19/2.99  --inst_restr_to_given                   false
% 19.19/2.99  --inst_activity_threshold               500
% 19.19/2.99  --inst_out_proof                        true
% 19.19/2.99  
% 19.19/2.99  ------ Resolution Options
% 19.19/2.99  
% 19.19/2.99  --resolution_flag                       true
% 19.19/2.99  --res_lit_sel                           adaptive
% 19.19/2.99  --res_lit_sel_side                      none
% 19.19/2.99  --res_ordering                          kbo
% 19.19/2.99  --res_to_prop_solver                    active
% 19.19/2.99  --res_prop_simpl_new                    false
% 19.19/2.99  --res_prop_simpl_given                  true
% 19.19/2.99  --res_passive_queue_type                priority_queues
% 19.19/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.19/2.99  --res_passive_queues_freq               [15;5]
% 19.19/2.99  --res_forward_subs                      full
% 19.19/2.99  --res_backward_subs                     full
% 19.19/2.99  --res_forward_subs_resolution           true
% 19.19/2.99  --res_backward_subs_resolution          true
% 19.19/2.99  --res_orphan_elimination                true
% 19.19/2.99  --res_time_limit                        2.
% 19.19/2.99  --res_out_proof                         true
% 19.19/2.99  
% 19.19/2.99  ------ Superposition Options
% 19.19/2.99  
% 19.19/2.99  --superposition_flag                    true
% 19.19/2.99  --sup_passive_queue_type                priority_queues
% 19.19/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.19/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.19/2.99  --demod_completeness_check              fast
% 19.19/2.99  --demod_use_ground                      true
% 19.19/2.99  --sup_to_prop_solver                    passive
% 19.19/2.99  --sup_prop_simpl_new                    true
% 19.19/2.99  --sup_prop_simpl_given                  true
% 19.19/2.99  --sup_fun_splitting                     true
% 19.19/2.99  --sup_smt_interval                      50000
% 19.19/2.99  
% 19.19/2.99  ------ Superposition Simplification Setup
% 19.19/2.99  
% 19.19/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.19/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.19/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.19/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.19/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.19/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.19/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.19/2.99  --sup_immed_triv                        [TrivRules]
% 19.19/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_immed_bw_main                     []
% 19.19/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.19/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.19/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_input_bw                          []
% 19.19/2.99  
% 19.19/2.99  ------ Combination Options
% 19.19/2.99  
% 19.19/2.99  --comb_res_mult                         3
% 19.19/2.99  --comb_sup_mult                         2
% 19.19/2.99  --comb_inst_mult                        10
% 19.19/2.99  
% 19.19/2.99  ------ Debug Options
% 19.19/2.99  
% 19.19/2.99  --dbg_backtrace                         false
% 19.19/2.99  --dbg_dump_prop_clauses                 false
% 19.19/2.99  --dbg_dump_prop_clauses_file            -
% 19.19/2.99  --dbg_out_stat                          false
% 19.19/2.99  ------ Parsing...
% 19.19/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.19/2.99  
% 19.19/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 19.19/2.99  
% 19.19/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.19/2.99  
% 19.19/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.19/2.99  ------ Proving...
% 19.19/2.99  ------ Problem Properties 
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  clauses                                 28
% 19.19/2.99  conjectures                             4
% 19.19/2.99  EPR                                     8
% 19.19/2.99  Horn                                    25
% 19.19/2.99  unary                                   10
% 19.19/2.99  binary                                  4
% 19.19/2.99  lits                                    65
% 19.19/2.99  lits eq                                 9
% 19.19/2.99  fd_pure                                 0
% 19.19/2.99  fd_pseudo                               0
% 19.19/2.99  fd_cond                                 0
% 19.19/2.99  fd_pseudo_cond                          2
% 19.19/2.99  AC symbols                              0
% 19.19/2.99  
% 19.19/2.99  ------ Schedule dynamic 5 is on 
% 19.19/2.99  
% 19.19/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  ------ 
% 19.19/2.99  Current options:
% 19.19/2.99  ------ 
% 19.19/2.99  
% 19.19/2.99  ------ Input Options
% 19.19/2.99  
% 19.19/2.99  --out_options                           all
% 19.19/2.99  --tptp_safe_out                         true
% 19.19/2.99  --problem_path                          ""
% 19.19/2.99  --include_path                          ""
% 19.19/2.99  --clausifier                            res/vclausify_rel
% 19.19/2.99  --clausifier_options                    ""
% 19.19/2.99  --stdin                                 false
% 19.19/2.99  --stats_out                             all
% 19.19/2.99  
% 19.19/2.99  ------ General Options
% 19.19/2.99  
% 19.19/2.99  --fof                                   false
% 19.19/2.99  --time_out_real                         305.
% 19.19/2.99  --time_out_virtual                      -1.
% 19.19/2.99  --symbol_type_check                     false
% 19.19/2.99  --clausify_out                          false
% 19.19/2.99  --sig_cnt_out                           false
% 19.19/2.99  --trig_cnt_out                          false
% 19.19/2.99  --trig_cnt_out_tolerance                1.
% 19.19/2.99  --trig_cnt_out_sk_spl                   false
% 19.19/2.99  --abstr_cl_out                          false
% 19.19/2.99  
% 19.19/2.99  ------ Global Options
% 19.19/2.99  
% 19.19/2.99  --schedule                              default
% 19.19/2.99  --add_important_lit                     false
% 19.19/2.99  --prop_solver_per_cl                    1000
% 19.19/2.99  --min_unsat_core                        false
% 19.19/2.99  --soft_assumptions                      false
% 19.19/2.99  --soft_lemma_size                       3
% 19.19/2.99  --prop_impl_unit_size                   0
% 19.19/2.99  --prop_impl_unit                        []
% 19.19/2.99  --share_sel_clauses                     true
% 19.19/2.99  --reset_solvers                         false
% 19.19/2.99  --bc_imp_inh                            [conj_cone]
% 19.19/2.99  --conj_cone_tolerance                   3.
% 19.19/2.99  --extra_neg_conj                        none
% 19.19/2.99  --large_theory_mode                     true
% 19.19/2.99  --prolific_symb_bound                   200
% 19.19/2.99  --lt_threshold                          2000
% 19.19/2.99  --clause_weak_htbl                      true
% 19.19/2.99  --gc_record_bc_elim                     false
% 19.19/2.99  
% 19.19/2.99  ------ Preprocessing Options
% 19.19/2.99  
% 19.19/2.99  --preprocessing_flag                    true
% 19.19/2.99  --time_out_prep_mult                    0.1
% 19.19/2.99  --splitting_mode                        input
% 19.19/2.99  --splitting_grd                         true
% 19.19/2.99  --splitting_cvd                         false
% 19.19/2.99  --splitting_cvd_svl                     false
% 19.19/2.99  --splitting_nvd                         32
% 19.19/2.99  --sub_typing                            true
% 19.19/2.99  --prep_gs_sim                           true
% 19.19/2.99  --prep_unflatten                        true
% 19.19/2.99  --prep_res_sim                          true
% 19.19/2.99  --prep_upred                            true
% 19.19/2.99  --prep_sem_filter                       exhaustive
% 19.19/2.99  --prep_sem_filter_out                   false
% 19.19/2.99  --pred_elim                             true
% 19.19/2.99  --res_sim_input                         true
% 19.19/2.99  --eq_ax_congr_red                       true
% 19.19/2.99  --pure_diseq_elim                       true
% 19.19/2.99  --brand_transform                       false
% 19.19/2.99  --non_eq_to_eq                          false
% 19.19/2.99  --prep_def_merge                        true
% 19.19/2.99  --prep_def_merge_prop_impl              false
% 19.19/2.99  --prep_def_merge_mbd                    true
% 19.19/2.99  --prep_def_merge_tr_red                 false
% 19.19/2.99  --prep_def_merge_tr_cl                  false
% 19.19/2.99  --smt_preprocessing                     true
% 19.19/2.99  --smt_ac_axioms                         fast
% 19.19/2.99  --preprocessed_out                      false
% 19.19/2.99  --preprocessed_stats                    false
% 19.19/2.99  
% 19.19/2.99  ------ Abstraction refinement Options
% 19.19/2.99  
% 19.19/2.99  --abstr_ref                             []
% 19.19/2.99  --abstr_ref_prep                        false
% 19.19/2.99  --abstr_ref_until_sat                   false
% 19.19/2.99  --abstr_ref_sig_restrict                funpre
% 19.19/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.19/2.99  --abstr_ref_under                       []
% 19.19/2.99  
% 19.19/2.99  ------ SAT Options
% 19.19/2.99  
% 19.19/2.99  --sat_mode                              false
% 19.19/2.99  --sat_fm_restart_options                ""
% 19.19/2.99  --sat_gr_def                            false
% 19.19/2.99  --sat_epr_types                         true
% 19.19/2.99  --sat_non_cyclic_types                  false
% 19.19/2.99  --sat_finite_models                     false
% 19.19/2.99  --sat_fm_lemmas                         false
% 19.19/2.99  --sat_fm_prep                           false
% 19.19/2.99  --sat_fm_uc_incr                        true
% 19.19/2.99  --sat_out_model                         small
% 19.19/2.99  --sat_out_clauses                       false
% 19.19/2.99  
% 19.19/2.99  ------ QBF Options
% 19.19/2.99  
% 19.19/2.99  --qbf_mode                              false
% 19.19/2.99  --qbf_elim_univ                         false
% 19.19/2.99  --qbf_dom_inst                          none
% 19.19/2.99  --qbf_dom_pre_inst                      false
% 19.19/2.99  --qbf_sk_in                             false
% 19.19/2.99  --qbf_pred_elim                         true
% 19.19/2.99  --qbf_split                             512
% 19.19/2.99  
% 19.19/2.99  ------ BMC1 Options
% 19.19/2.99  
% 19.19/2.99  --bmc1_incremental                      false
% 19.19/2.99  --bmc1_axioms                           reachable_all
% 19.19/2.99  --bmc1_min_bound                        0
% 19.19/2.99  --bmc1_max_bound                        -1
% 19.19/2.99  --bmc1_max_bound_default                -1
% 19.19/2.99  --bmc1_symbol_reachability              true
% 19.19/2.99  --bmc1_property_lemmas                  false
% 19.19/2.99  --bmc1_k_induction                      false
% 19.19/2.99  --bmc1_non_equiv_states                 false
% 19.19/2.99  --bmc1_deadlock                         false
% 19.19/2.99  --bmc1_ucm                              false
% 19.19/2.99  --bmc1_add_unsat_core                   none
% 19.19/2.99  --bmc1_unsat_core_children              false
% 19.19/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.19/2.99  --bmc1_out_stat                         full
% 19.19/2.99  --bmc1_ground_init                      false
% 19.19/2.99  --bmc1_pre_inst_next_state              false
% 19.19/2.99  --bmc1_pre_inst_state                   false
% 19.19/2.99  --bmc1_pre_inst_reach_state             false
% 19.19/2.99  --bmc1_out_unsat_core                   false
% 19.19/2.99  --bmc1_aig_witness_out                  false
% 19.19/2.99  --bmc1_verbose                          false
% 19.19/2.99  --bmc1_dump_clauses_tptp                false
% 19.19/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.19/2.99  --bmc1_dump_file                        -
% 19.19/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.19/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.19/2.99  --bmc1_ucm_extend_mode                  1
% 19.19/2.99  --bmc1_ucm_init_mode                    2
% 19.19/2.99  --bmc1_ucm_cone_mode                    none
% 19.19/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.19/2.99  --bmc1_ucm_relax_model                  4
% 19.19/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.19/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.19/2.99  --bmc1_ucm_layered_model                none
% 19.19/2.99  --bmc1_ucm_max_lemma_size               10
% 19.19/2.99  
% 19.19/2.99  ------ AIG Options
% 19.19/2.99  
% 19.19/2.99  --aig_mode                              false
% 19.19/2.99  
% 19.19/2.99  ------ Instantiation Options
% 19.19/2.99  
% 19.19/2.99  --instantiation_flag                    true
% 19.19/2.99  --inst_sos_flag                         true
% 19.19/2.99  --inst_sos_phase                        true
% 19.19/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.19/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.19/2.99  --inst_lit_sel_side                     none
% 19.19/2.99  --inst_solver_per_active                1400
% 19.19/2.99  --inst_solver_calls_frac                1.
% 19.19/2.99  --inst_passive_queue_type               priority_queues
% 19.19/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.19/2.99  --inst_passive_queues_freq              [25;2]
% 19.19/2.99  --inst_dismatching                      true
% 19.19/2.99  --inst_eager_unprocessed_to_passive     true
% 19.19/2.99  --inst_prop_sim_given                   true
% 19.19/2.99  --inst_prop_sim_new                     false
% 19.19/2.99  --inst_subs_new                         false
% 19.19/2.99  --inst_eq_res_simp                      false
% 19.19/2.99  --inst_subs_given                       false
% 19.19/2.99  --inst_orphan_elimination               true
% 19.19/2.99  --inst_learning_loop_flag               true
% 19.19/2.99  --inst_learning_start                   3000
% 19.19/2.99  --inst_learning_factor                  2
% 19.19/2.99  --inst_start_prop_sim_after_learn       3
% 19.19/2.99  --inst_sel_renew                        solver
% 19.19/2.99  --inst_lit_activity_flag                true
% 19.19/2.99  --inst_restr_to_given                   false
% 19.19/2.99  --inst_activity_threshold               500
% 19.19/2.99  --inst_out_proof                        true
% 19.19/2.99  
% 19.19/2.99  ------ Resolution Options
% 19.19/2.99  
% 19.19/2.99  --resolution_flag                       false
% 19.19/2.99  --res_lit_sel                           adaptive
% 19.19/2.99  --res_lit_sel_side                      none
% 19.19/2.99  --res_ordering                          kbo
% 19.19/2.99  --res_to_prop_solver                    active
% 19.19/2.99  --res_prop_simpl_new                    false
% 19.19/2.99  --res_prop_simpl_given                  true
% 19.19/2.99  --res_passive_queue_type                priority_queues
% 19.19/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.19/2.99  --res_passive_queues_freq               [15;5]
% 19.19/2.99  --res_forward_subs                      full
% 19.19/2.99  --res_backward_subs                     full
% 19.19/2.99  --res_forward_subs_resolution           true
% 19.19/2.99  --res_backward_subs_resolution          true
% 19.19/2.99  --res_orphan_elimination                true
% 19.19/2.99  --res_time_limit                        2.
% 19.19/2.99  --res_out_proof                         true
% 19.19/2.99  
% 19.19/2.99  ------ Superposition Options
% 19.19/2.99  
% 19.19/2.99  --superposition_flag                    true
% 19.19/2.99  --sup_passive_queue_type                priority_queues
% 19.19/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.19/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.19/2.99  --demod_completeness_check              fast
% 19.19/2.99  --demod_use_ground                      true
% 19.19/2.99  --sup_to_prop_solver                    passive
% 19.19/2.99  --sup_prop_simpl_new                    true
% 19.19/2.99  --sup_prop_simpl_given                  true
% 19.19/2.99  --sup_fun_splitting                     true
% 19.19/2.99  --sup_smt_interval                      50000
% 19.19/2.99  
% 19.19/2.99  ------ Superposition Simplification Setup
% 19.19/2.99  
% 19.19/2.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 19.19/2.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 19.19/2.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 19.19/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 19.19/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.19/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 19.19/2.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 19.19/2.99  --sup_immed_triv                        [TrivRules]
% 19.19/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_immed_bw_main                     []
% 19.19/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 19.19/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.19/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 19.19/2.99  --sup_input_bw                          []
% 19.19/2.99  
% 19.19/2.99  ------ Combination Options
% 19.19/2.99  
% 19.19/2.99  --comb_res_mult                         3
% 19.19/2.99  --comb_sup_mult                         2
% 19.19/2.99  --comb_inst_mult                        10
% 19.19/2.99  
% 19.19/2.99  ------ Debug Options
% 19.19/2.99  
% 19.19/2.99  --dbg_backtrace                         false
% 19.19/2.99  --dbg_dump_prop_clauses                 false
% 19.19/2.99  --dbg_dump_prop_clauses_file            -
% 19.19/2.99  --dbg_out_stat                          false
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  ------ Proving...
% 19.19/2.99  
% 19.19/2.99  
% 19.19/2.99  % SZS status Theorem for theBenchmark.p
% 19.19/2.99  
% 19.19/2.99   Resolution empty clause
% 19.19/2.99  
% 19.19/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.19/2.99  
% 19.19/2.99  fof(f14,conjecture,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f15,negated_conjecture,(
% 19.19/2.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 19.19/2.99    inference(negated_conjecture,[],[f14])).
% 19.19/2.99  
% 19.19/2.99  fof(f30,plain,(
% 19.19/2.99    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f15])).
% 19.19/2.99  
% 19.19/2.99  fof(f31,plain,(
% 19.19/2.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 19.19/2.99    inference(flattening,[],[f30])).
% 19.19/2.99  
% 19.19/2.99  fof(f44,plain,(
% 19.19/2.99    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK3,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK3,X0))) )),
% 19.19/2.99    introduced(choice_axiom,[])).
% 19.19/2.99  
% 19.19/2.99  fof(f43,plain,(
% 19.19/2.99    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK2,X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK2,X0))) )),
% 19.19/2.99    introduced(choice_axiom,[])).
% 19.19/2.99  
% 19.19/2.99  fof(f42,plain,(
% 19.19/2.99    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK1) & v1_tex_2(X1,sK1) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK1)) & m1_pre_topc(X1,sK1)) & l1_pre_topc(sK1))),
% 19.19/2.99    introduced(choice_axiom,[])).
% 19.19/2.99  
% 19.19/2.99  fof(f45,plain,(
% 19.19/2.99    ((~v1_tex_2(sK3,sK1) & v1_tex_2(sK2,sK1) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK1)) & m1_pre_topc(sK2,sK1)) & l1_pre_topc(sK1)),
% 19.19/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f31,f44,f43,f42])).
% 19.19/2.99  
% 19.19/2.99  fof(f69,plain,(
% 19.19/2.99    l1_pre_topc(sK1)),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f6,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f21,plain,(
% 19.19/2.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f6])).
% 19.19/2.99  
% 19.19/2.99  fof(f56,plain,(
% 19.19/2.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f21])).
% 19.19/2.99  
% 19.19/2.99  fof(f4,axiom,(
% 19.19/2.99    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f18,plain,(
% 19.19/2.99    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f4])).
% 19.19/2.99  
% 19.19/2.99  fof(f53,plain,(
% 19.19/2.99    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f18])).
% 19.19/2.99  
% 19.19/2.99  fof(f71,plain,(
% 19.19/2.99    m1_pre_topc(sK3,sK1)),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f7,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f22,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f7])).
% 19.19/2.99  
% 19.19/2.99  fof(f57,plain,(
% 19.19/2.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f22])).
% 19.19/2.99  
% 19.19/2.99  fof(f11,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f26,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f11])).
% 19.19/2.99  
% 19.19/2.99  fof(f62,plain,(
% 19.19/2.99    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f26])).
% 19.19/2.99  
% 19.19/2.99  fof(f12,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f27,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f12])).
% 19.19/2.99  
% 19.19/2.99  fof(f28,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(flattening,[],[f27])).
% 19.19/2.99  
% 19.19/2.99  fof(f37,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(nnf_transformation,[],[f28])).
% 19.19/2.99  
% 19.19/2.99  fof(f38,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(rectify,[],[f37])).
% 19.19/2.99  
% 19.19/2.99  fof(f39,plain,(
% 19.19/2.99    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.19/2.99    introduced(choice_axiom,[])).
% 19.19/2.99  
% 19.19/2.99  fof(f40,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 19.19/2.99  
% 19.19/2.99  fof(f64,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f40])).
% 19.19/2.99  
% 19.19/2.99  fof(f74,plain,(
% 19.19/2.99    ~v1_tex_2(sK3,sK1)),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f65,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f40])).
% 19.19/2.99  
% 19.19/2.99  fof(f2,axiom,(
% 19.19/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f34,plain,(
% 19.19/2.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.19/2.99    inference(nnf_transformation,[],[f2])).
% 19.19/2.99  
% 19.19/2.99  fof(f49,plain,(
% 19.19/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.19/2.99    inference(cnf_transformation,[],[f34])).
% 19.19/2.99  
% 19.19/2.99  fof(f1,axiom,(
% 19.19/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f32,plain,(
% 19.19/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.19/2.99    inference(nnf_transformation,[],[f1])).
% 19.19/2.99  
% 19.19/2.99  fof(f33,plain,(
% 19.19/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.19/2.99    inference(flattening,[],[f32])).
% 19.19/2.99  
% 19.19/2.99  fof(f48,plain,(
% 19.19/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f33])).
% 19.19/2.99  
% 19.19/2.99  fof(f66,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f40])).
% 19.19/2.99  
% 19.19/2.99  fof(f13,axiom,(
% 19.19/2.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f29,plain,(
% 19.19/2.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/2.99    inference(ennf_transformation,[],[f13])).
% 19.19/2.99  
% 19.19/2.99  fof(f41,plain,(
% 19.19/2.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 19.19/2.99    inference(nnf_transformation,[],[f29])).
% 19.19/2.99  
% 19.19/2.99  fof(f68,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/2.99    inference(cnf_transformation,[],[f41])).
% 19.19/2.99  
% 19.19/2.99  fof(f50,plain,(
% 19.19/2.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f34])).
% 19.19/2.99  
% 19.19/2.99  fof(f5,axiom,(
% 19.19/2.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f19,plain,(
% 19.19/2.99    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 19.19/2.99    inference(ennf_transformation,[],[f5])).
% 19.19/2.99  
% 19.19/2.99  fof(f20,plain,(
% 19.19/2.99    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(flattening,[],[f19])).
% 19.19/2.99  
% 19.19/2.99  fof(f55,plain,(
% 19.19/2.99    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f20])).
% 19.19/2.99  
% 19.19/2.99  fof(f9,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f24,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f9])).
% 19.19/2.99  
% 19.19/2.99  fof(f36,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(nnf_transformation,[],[f24])).
% 19.19/2.99  
% 19.19/2.99  fof(f59,plain,(
% 19.19/2.99    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f36])).
% 19.19/2.99  
% 19.19/2.99  fof(f70,plain,(
% 19.19/2.99    m1_pre_topc(sK2,sK1)),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f8,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f23,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f8])).
% 19.19/2.99  
% 19.19/2.99  fof(f58,plain,(
% 19.19/2.99    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f23])).
% 19.19/2.99  
% 19.19/2.99  fof(f72,plain,(
% 19.19/2.99    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f46,plain,(
% 19.19/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 19.19/2.99    inference(cnf_transformation,[],[f33])).
% 19.19/2.99  
% 19.19/2.99  fof(f76,plain,(
% 19.19/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.19/2.99    inference(equality_resolution,[],[f46])).
% 19.19/2.99  
% 19.19/2.99  fof(f3,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f16,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f3])).
% 19.19/2.99  
% 19.19/2.99  fof(f17,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(flattening,[],[f16])).
% 19.19/2.99  
% 19.19/2.99  fof(f35,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(nnf_transformation,[],[f17])).
% 19.19/2.99  
% 19.19/2.99  fof(f51,plain,(
% 19.19/2.99    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f35])).
% 19.19/2.99  
% 19.19/2.99  fof(f78,plain,(
% 19.19/2.99    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(equality_resolution,[],[f51])).
% 19.19/2.99  
% 19.19/2.99  fof(f54,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f20])).
% 19.19/2.99  
% 19.19/2.99  fof(f63,plain,(
% 19.19/2.99    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f40])).
% 19.19/2.99  
% 19.19/2.99  fof(f79,plain,(
% 19.19/2.99    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(equality_resolution,[],[f63])).
% 19.19/2.99  
% 19.19/2.99  fof(f10,axiom,(
% 19.19/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.19/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.19/2.99  
% 19.19/2.99  fof(f25,plain,(
% 19.19/2.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.19/2.99    inference(ennf_transformation,[],[f10])).
% 19.19/2.99  
% 19.19/2.99  fof(f61,plain,(
% 19.19/2.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.19/2.99    inference(cnf_transformation,[],[f25])).
% 19.19/2.99  
% 19.19/2.99  fof(f73,plain,(
% 19.19/2.99    v1_tex_2(sK2,sK1)),
% 19.19/2.99    inference(cnf_transformation,[],[f45])).
% 19.19/2.99  
% 19.19/2.99  fof(f67,plain,(
% 19.19/2.99    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 19.19/2.99    inference(cnf_transformation,[],[f41])).
% 19.19/2.99  
% 19.19/2.99  fof(f80,plain,(
% 19.19/2.99    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 19.19/2.99    inference(equality_resolution,[],[f67])).
% 19.19/2.99  
% 19.19/2.99  cnf(c_28,negated_conjecture,
% 19.19/2.99      ( l1_pre_topc(sK1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f69]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2570,plain,
% 19.19/2.99      ( l1_pre_topc(sK1) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_10,plain,
% 19.19/2.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_7,plain,
% 19.19/2.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_383,plain,
% 19.19/2.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 19.19/2.99      inference(resolution,[status(thm)],[c_10,c_7]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2566,plain,
% 19.19/2.99      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_pre_topc(X0) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_383]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3371,plain,
% 19.19/2.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_2570,c_2566]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_26,negated_conjecture,
% 19.19/2.99      ( m1_pre_topc(sK3,sK1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f71]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2572,plain,
% 19.19/2.99      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_11,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2577,plain,
% 19.19/2.99      ( m1_pre_topc(X0,X1) != iProver_top
% 19.19/2.99      | l1_pre_topc(X1) != iProver_top
% 19.19/2.99      | l1_pre_topc(X0) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3796,plain,
% 19.19/2.99      ( l1_pre_topc(sK1) != iProver_top | l1_pre_topc(sK3) = iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_2572,c_2577]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_29,plain,
% 19.19/2.99      ( l1_pre_topc(sK1) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3978,plain,
% 19.19/2.99      ( l1_pre_topc(sK3) = iProver_top ),
% 19.19/2.99      inference(global_propositional_subsumption,[status(thm)],[c_3796,c_29]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3982,plain,
% 19.19/2.99      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3978,c_2566]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_16,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.19/2.99      | ~ l1_pre_topc(X1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2574,plain,
% 19.19/2.99      ( m1_pre_topc(X0,X1) != iProver_top
% 19.19/2.99      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 19.19/2.99      | l1_pre_topc(X1) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4084,plain,
% 19.19/2.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 19.19/2.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 19.19/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3982,c_2574]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8044,plain,
% 19.19/2.99      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top
% 19.19/2.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_4084,c_29,c_3796]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8045,plain,
% 19.19/2.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 19.19/2.99      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK3)) = iProver_top ),
% 19.19/2.99      inference(renaming,[status(thm)],[c_8044]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8052,plain,
% 19.19/2.99      ( m1_pre_topc(sK1,sK3) != iProver_top
% 19.19/2.99      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK3)) = iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3371,c_8045]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_19,plain,
% 19.19/2.99      ( v1_tex_2(X0,X1)
% 19.19/2.99      | ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/2.99      | ~ l1_pre_topc(X1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_23,negated_conjecture,
% 19.19/2.99      ( ~ v1_tex_2(sK3,sK1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f74]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_579,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/2.99      | ~ l1_pre_topc(X1)
% 19.19/2.99      | sK1 != X1
% 19.19/2.99      | sK3 != X0 ),
% 19.19/2.99      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_580,plain,
% 19.19/2.99      ( ~ m1_pre_topc(sK3,sK1)
% 19.19/2.99      | m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
% 19.19/2.99      | ~ l1_pre_topc(sK1) ),
% 19.19/2.99      inference(unflattening,[status(thm)],[c_579]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_582,plain,
% 19.19/2.99      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_580,c_28,c_26]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2561,plain,
% 19.19/2.99      ( m1_subset_1(sK0(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_18,plain,
% 19.19/2.99      ( v1_tex_2(X0,X1)
% 19.19/2.99      | ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | ~ l1_pre_topc(X1)
% 19.19/2.99      | sK0(X1,X0) = u1_struct_0(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_590,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | ~ l1_pre_topc(X1)
% 19.19/2.99      | sK0(X1,X0) = u1_struct_0(X0)
% 19.19/2.99      | sK1 != X1
% 19.19/2.99      | sK3 != X0 ),
% 19.19/2.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_591,plain,
% 19.19/2.99      ( ~ m1_pre_topc(sK3,sK1)
% 19.19/2.99      | ~ l1_pre_topc(sK1)
% 19.19/2.99      | sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 19.19/2.99      inference(unflattening,[status(thm)],[c_590]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_593,plain,
% 19.19/2.99      ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_591,c_28,c_26]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2585,plain,
% 19.19/2.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 19.19/2.99      inference(light_normalisation,[status(thm)],[c_2561,c_593]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4,plain,
% 19.19/2.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2581,plain,
% 19.19/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 19.19/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3202,plain,
% 19.19/2.99      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_2585,c_2581]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3469,plain,
% 19.19/2.99      ( r1_tarski(u1_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3371,c_3202]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_0,plain,
% 19.19/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.19/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2584,plain,
% 19.19/2.99      ( X0 = X1
% 19.19/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.19/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3802,plain,
% 19.19/2.99      ( u1_struct_0(sK3) = k2_struct_0(sK1)
% 19.19/2.99      | r1_tarski(k2_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3469,c_2584]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_5358,plain,
% 19.19/2.99      ( k2_struct_0(sK3) = k2_struct_0(sK1)
% 19.19/2.99      | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK3)) != iProver_top ),
% 19.19/2.99      inference(light_normalisation,[status(thm)],[c_3802,c_3982]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8213,plain,
% 19.19/2.99      ( k2_struct_0(sK3) = k2_struct_0(sK1)
% 19.19/2.99      | m1_pre_topc(sK1,sK3) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_8052,c_5358]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_17,plain,
% 19.19/2.99      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 19.19/2.99      | v1_tex_2(X1,X0)
% 19.19/2.99      | ~ m1_pre_topc(X1,X0)
% 19.19/2.99      | ~ l1_pre_topc(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_568,plain,
% 19.19/2.99      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 19.19/2.99      | ~ m1_pre_topc(X1,X0)
% 19.19/2.99      | ~ l1_pre_topc(X0)
% 19.19/2.99      | sK1 != X0
% 19.19/2.99      | sK3 != X1 ),
% 19.19/2.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_569,plain,
% 19.19/2.99      ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1))
% 19.19/2.99      | ~ m1_pre_topc(sK3,sK1)
% 19.19/2.99      | ~ l1_pre_topc(sK1) ),
% 19.19/2.99      inference(unflattening,[status(thm)],[c_568]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_571,plain,
% 19.19/2.99      ( ~ v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_569,c_28,c_26]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2562,plain,
% 19.19/2.99      ( v1_subset_1(sK0(sK1,sK3),u1_struct_0(sK1)) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2586,plain,
% 19.19/2.99      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top ),
% 19.19/2.99      inference(light_normalisation,[status(thm)],[c_2562,c_593]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3470,plain,
% 19.19/2.99      ( v1_subset_1(u1_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3371,c_2586]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4071,plain,
% 19.19/2.99      ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK1)) != iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3982,c_3470]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4072,plain,
% 19.19/2.99      ( r1_tarski(k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3982,c_3469]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_21,plain,
% 19.19/2.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 19.19/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3,plain,
% 19.19/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_240,plain,
% 19.19/2.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.19/2.99      inference(prop_impl,[status(thm)],[c_3]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_241,plain,
% 19.19/2.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 19.19/2.99      inference(renaming,[status(thm)],[c_240]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_288,plain,
% 19.19/2.99      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 19.19/2.99      inference(bin_hyper_res,[status(thm)],[c_21,c_241]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2567,plain,
% 19.19/2.99      ( X0 = X1
% 19.19/2.99      | v1_subset_1(X0,X1) = iProver_top
% 19.19/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_7522,plain,
% 19.19/2.99      ( k2_struct_0(sK3) = k2_struct_0(sK1)
% 19.19/2.99      | v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK1)) = iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_4072,c_2567]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8404,plain,
% 19.19/2.99      ( k2_struct_0(sK3) = k2_struct_0(sK1) ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_8213,c_4071,c_7522]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3471,plain,
% 19.19/2.99      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3371,c_2585]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4070,plain,
% 19.19/2.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK1))) = iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_3982,c_3471]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8414,plain,
% 19.19/2.99      ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) = iProver_top ),
% 19.19/2.99      inference(demodulation,[status(thm)],[c_8404,c_4070]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_8,plain,
% 19.19/2.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 19.19/2.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.19/2.99      | ~ l1_pre_topc(X0) ),
% 19.19/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2579,plain,
% 19.19/2.99      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 19.19/2.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.19/2.99      | l1_pre_topc(X0) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_4555,plain,
% 19.19/2.99      ( m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top
% 19.19/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 19.19/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3982,c_2579]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_15803,plain,
% 19.19/2.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top
% 19.19/2.99      | m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_4555,c_29,c_3796]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_15804,plain,
% 19.19/2.99      ( m1_pre_topc(k1_pre_topc(sK3,X0),sK3) = iProver_top
% 19.19/2.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 19.19/2.99      inference(renaming,[status(thm)],[c_15803]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_55811,plain,
% 19.19/2.99      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK3) = iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_8414,c_15804]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_14,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.19/2.99      | ~ l1_pre_topc(X0)
% 19.19/2.99      | ~ l1_pre_topc(X1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_173,plain,
% 19.19/2.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.19/2.99      | ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | ~ l1_pre_topc(X1) ),
% 19.19/2.99      inference(global_propositional_subsumption,[status(thm)],[c_14,c_11]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_174,plain,
% 19.19/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.19/2.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.19/2.99      | ~ l1_pre_topc(X1) ),
% 19.19/2.99      inference(renaming,[status(thm)],[c_173]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2569,plain,
% 19.19/2.99      ( m1_pre_topc(X0,X1) != iProver_top
% 19.19/2.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 19.19/2.99      | l1_pre_topc(X1) != iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_6178,plain,
% 19.19/2.99      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.19/2.99      | m1_pre_topc(X0,sK3) != iProver_top
% 19.19/2.99      | l1_pre_topc(sK3) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_3982,c_2569]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_17247,plain,
% 19.19/2.99      ( m1_pre_topc(X0,sK3) != iProver_top
% 19.19/2.99      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 19.19/2.99      inference(global_propositional_subsumption,
% 19.19/2.99                [status(thm)],
% 19.19/2.99                [c_6178,c_29,c_3796]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_17248,plain,
% 19.19/2.99      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 19.19/2.99      | m1_pre_topc(X0,sK3) != iProver_top ),
% 19.19/2.99      inference(renaming,[status(thm)],[c_17247]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_27,negated_conjecture,
% 19.19/2.99      ( m1_pre_topc(sK2,sK1) ),
% 19.19/2.99      inference(cnf_transformation,[],[f70]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_2571,plain,
% 19.19/2.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 19.19/2.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3797,plain,
% 19.19/2.99      ( l1_pre_topc(sK2) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 19.19/2.99      inference(superposition,[status(thm)],[c_2571,c_2577]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3984,plain,
% 19.19/2.99      ( l1_pre_topc(sK2) = iProver_top ),
% 19.19/2.99      inference(global_propositional_subsumption,[status(thm)],[c_3797,c_29]) ).
% 19.19/2.99  
% 19.19/2.99  cnf(c_3988,plain,
% 19.19/3.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3984,c_2566]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_12,plain,
% 19.19/3.00      ( m1_pre_topc(X0,X1)
% 19.19/3.00      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f58]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2576,plain,
% 19.19/3.00      ( m1_pre_topc(X0,X1) = iProver_top
% 19.19/3.00      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4537,plain,
% 19.19/3.00      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK2) = iProver_top
% 19.19/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3988,c_2576]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_25,negated_conjecture,
% 19.19/3.00      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f72]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4074,plain,
% 19.19/3.00      ( g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_3982,c_25]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4075,plain,
% 19.19/3.00      ( g1_pre_topc(k2_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3)) ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_4074,c_3988]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4540,plain,
% 19.19/3.00      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK2) = iProver_top
% 19.19/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_4537,c_4075]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5077,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 19.19/3.00      | m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_4540,c_29,c_3797]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5078,plain,
% 19.19/3.00      ( m1_pre_topc(X0,g1_pre_topc(k2_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK2) = iProver_top ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_5077]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_17254,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK2) = iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK3) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_17248,c_5078]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_59456,plain,
% 19.19/3.00      ( m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) = iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_55811,c_17254]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3867,plain,
% 19.19/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.19/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.19/3.00      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2574,c_2584]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_7113,plain,
% 19.19/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.19/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.19/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2574,c_3867]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_65,plain,
% 19.19/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_22187,plain,
% 19.19/3.00      ( m1_pre_topc(X0,X1) != iProver_top
% 19.19/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.19/3.00      | u1_struct_0(X0) = u1_struct_0(X1)
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_7113,c_65]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_22188,plain,
% 19.19/3.00      ( u1_struct_0(X0) = u1_struct_0(X1)
% 19.19/3.00      | m1_pre_topc(X0,X1) != iProver_top
% 19.19/3.00      | m1_pre_topc(X1,X0) != iProver_top
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_22187]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_60959,plain,
% 19.19/3.00      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = u1_struct_0(sK2)
% 19.19/3.00      | m1_pre_topc(sK2,k1_pre_topc(sK3,k2_struct_0(sK3))) != iProver_top
% 19.19/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_59456,c_22188]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f76]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2583,plain,
% 19.19/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2582,plain,
% 19.19/3.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 19.19/3.00      | r1_tarski(X0,X1) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4551,plain,
% 19.19/3.00      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 19.19/3.00      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2582,c_2579]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_12539,plain,
% 19.19/3.00      ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 19.19/3.00      | l1_pre_topc(X1) != iProver_top
% 19.19/3.00      | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_4551,c_2577]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_13406,plain,
% 19.19/3.00      ( l1_pre_topc(X0) != iProver_top
% 19.19/3.00      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2583,c_12539]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_13428,plain,
% 19.19/3.00      ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top
% 19.19/3.00      | l1_pre_topc(sK3) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3982,c_13406]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_13688,plain,
% 19.19/3.00      ( l1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3))) = iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_13428,c_29,c_3796]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_13693,plain,
% 19.19/3.00      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_13688,c_2566]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_6,plain,
% 19.19/3.00      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 19.19/3.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.19/3.00      | ~ l1_pre_topc(X0)
% 19.19/3.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 19.19/3.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 19.19/3.00      inference(cnf_transformation,[],[f78]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_189,plain,
% 19.19/3.00      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 19.19/3.00      | ~ l1_pre_topc(X0)
% 19.19/3.00      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
% 19.19/3.00      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_6,c_8]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_190,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1)
% 19.19/3.00      | ~ v1_pre_topc(k1_pre_topc(X1,X0))
% 19.19/3.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_189]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_9,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1)
% 19.19/3.00      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f54]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_195,plain,
% 19.19/3.00      ( ~ l1_pre_topc(X1)
% 19.19/3.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_190,c_9]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_196,plain,
% 19.19/3.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1)
% 19.19/3.00      | k2_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_195]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2568,plain,
% 19.19/3.00      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 19.19/3.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_196]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5209,plain,
% 19.19/3.00      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
% 19.19/3.00      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2582,c_2568]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_10729,plain,
% 19.19/3.00      ( k2_struct_0(k1_pre_topc(X0,u1_struct_0(X0))) = u1_struct_0(X0)
% 19.19/3.00      | l1_pre_topc(X0) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2583,c_5209]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_10748,plain,
% 19.19/3.00      ( k2_struct_0(k1_pre_topc(sK3,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3978,c_10729]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_10755,plain,
% 19.19/3.00      ( k2_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_10748,c_3982]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_13694,plain,
% 19.19/3.00      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK3) ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_13693,c_10755]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_60968,plain,
% 19.19/3.00      ( k2_struct_0(sK3) = k2_struct_0(sK2)
% 19.19/3.00      | m1_pre_topc(sK2,k1_pre_topc(sK3,k2_struct_0(sK3))) != iProver_top
% 19.19/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_60959,c_3988,c_13694]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3866,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 19.19/3.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
% 19.19/3.00      | l1_pre_topc(sK1) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3371,c_2574]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4326,plain,
% 19.19/3.00      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK1) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_3866,c_29]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4327,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK1) != iProver_top
% 19.19/3.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_4326]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4332,plain,
% 19.19/3.00      ( m1_pre_topc(sK2,sK1) != iProver_top
% 19.19/3.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3988,c_4327]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_30,plain,
% 19.19/3.00      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_6930,plain,
% 19.19/3.00      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_4332,c_30]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_8412,plain,
% 19.19/3.00      ( r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_8404,c_6930]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4209,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 19.19/3.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 19.19/3.00      | l1_pre_topc(sK2) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_3988,c_2574]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_9512,plain,
% 19.19/3.00      ( r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top
% 19.19/3.00      | m1_pre_topc(X0,sK2) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_4209,c_29,c_3797]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_9513,plain,
% 19.19/3.00      ( m1_pre_topc(X0,sK2) != iProver_top
% 19.19/3.00      | r1_tarski(u1_struct_0(X0),k2_struct_0(sK2)) = iProver_top ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_9512]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_9522,plain,
% 19.19/3.00      ( u1_struct_0(X0) = k2_struct_0(sK2)
% 19.19/3.00      | m1_pre_topc(X0,sK2) != iProver_top
% 19.19/3.00      | r1_tarski(k2_struct_0(sK2),u1_struct_0(X0)) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_9513,c_2584]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_58386,plain,
% 19.19/3.00      ( u1_struct_0(k1_pre_topc(sK3,k2_struct_0(sK3))) = k2_struct_0(sK2)
% 19.19/3.00      | m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
% 19.19/3.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_13694,c_9522]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_58483,plain,
% 19.19/3.00      ( k2_struct_0(sK3) = k2_struct_0(sK2)
% 19.19/3.00      | m1_pre_topc(k1_pre_topc(sK3,k2_struct_0(sK3)),sK2) != iProver_top
% 19.19/3.00      | r1_tarski(k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top ),
% 19.19/3.00      inference(light_normalisation,[status(thm)],[c_58386,c_13694]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_61242,plain,
% 19.19/3.00      ( k2_struct_0(sK3) = k2_struct_0(sK2) ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_60968,c_8412,c_58483,c_59456]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_20,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 19.19/3.00      | ~ v1_tex_2(X0,X1)
% 19.19/3.00      | ~ m1_pre_topc(X0,X1)
% 19.19/3.00      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f79]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_15,plain,
% 19.19/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.19/3.00      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.19/3.00      | ~ l1_pre_topc(X1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_161,plain,
% 19.19/3.00      ( ~ m1_pre_topc(X0,X1)
% 19.19/3.00      | ~ v1_tex_2(X0,X1)
% 19.19/3.00      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 19.19/3.00      | ~ l1_pre_topc(X1) ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_20,c_15]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_162,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 19.19/3.00      | ~ v1_tex_2(X0,X1)
% 19.19/3.00      | ~ m1_pre_topc(X0,X1)
% 19.19/3.00      | ~ l1_pre_topc(X1) ),
% 19.19/3.00      inference(renaming,[status(thm)],[c_161]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_24,negated_conjecture,
% 19.19/3.00      ( v1_tex_2(sK2,sK1) ),
% 19.19/3.00      inference(cnf_transformation,[],[f73]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_598,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 19.19/3.00      | ~ m1_pre_topc(X0,X1)
% 19.19/3.00      | ~ l1_pre_topc(X1)
% 19.19/3.00      | sK2 != X0
% 19.19/3.00      | sK1 != X1 ),
% 19.19/3.00      inference(resolution_lifted,[status(thm)],[c_162,c_24]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_599,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 19.19/3.00      | ~ m1_pre_topc(sK2,sK1)
% 19.19/3.00      | ~ l1_pre_topc(sK1) ),
% 19.19/3.00      inference(unflattening,[status(thm)],[c_598]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_601,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 19.19/3.00      inference(global_propositional_subsumption,
% 19.19/3.00                [status(thm)],
% 19.19/3.00                [c_599,c_28,c_27]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2560,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3472,plain,
% 19.19/3.00      ( v1_subset_1(u1_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_3371,c_2560]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_4202,plain,
% 19.19/3.00      ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK1)) = iProver_top ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_3988,c_3472]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_8415,plain,
% 19.19/3.00      ( v1_subset_1(k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_8404,c_4202]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_61260,plain,
% 19.19/3.00      ( v1_subset_1(k2_struct_0(sK3),k2_struct_0(sK3)) = iProver_top ),
% 19.19/3.00      inference(demodulation,[status(thm)],[c_61242,c_8415]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_22,plain,
% 19.19/3.00      ( ~ v1_subset_1(X0,X0) | ~ m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 19.19/3.00      inference(cnf_transformation,[],[f80]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_2573,plain,
% 19.19/3.00      ( v1_subset_1(X0,X0) != iProver_top
% 19.19/3.00      | m1_subset_1(X0,k1_zfmisc_1(X0)) != iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_3285,plain,
% 19.19/3.00      ( v1_subset_1(X0,X0) != iProver_top | r1_tarski(X0,X0) != iProver_top ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_2582,c_2573]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_90,plain,
% 19.19/3.00      ( r1_tarski(X0,X0) = iProver_top ),
% 19.19/3.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_5238,plain,
% 19.19/3.00      ( v1_subset_1(X0,X0) != iProver_top ),
% 19.19/3.00      inference(global_propositional_subsumption,[status(thm)],[c_3285,c_90]) ).
% 19.19/3.00  
% 19.19/3.00  cnf(c_62478,plain,
% 19.19/3.00      ( $false ),
% 19.19/3.00      inference(superposition,[status(thm)],[c_61260,c_5238]) ).
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.19/3.00  
% 19.19/3.00  ------                               Statistics
% 19.19/3.00  
% 19.19/3.00  ------ General
% 19.19/3.00  
% 19.19/3.00  abstr_ref_over_cycles:                  0
% 19.19/3.00  abstr_ref_under_cycles:                 0
% 19.19/3.00  gc_basic_clause_elim:                   0
% 19.19/3.00  forced_gc_time:                         0
% 19.19/3.00  parsing_time:                           0.015
% 19.19/3.00  unif_index_cands_time:                  0.
% 19.19/3.00  unif_index_add_time:                    0.
% 19.19/3.00  orderings_time:                         0.
% 19.19/3.00  out_proof_time:                         0.018
% 19.19/3.00  total_time:                             2.182
% 19.19/3.00  num_of_symbols:                         49
% 19.19/3.00  num_of_terms:                           30673
% 19.19/3.00  
% 19.19/3.00  ------ Preprocessing
% 19.19/3.00  
% 19.19/3.00  num_of_splits:                          0
% 19.19/3.00  num_of_split_atoms:                     0
% 19.19/3.00  num_of_reused_defs:                     0
% 19.19/3.00  num_eq_ax_congr_red:                    6
% 19.19/3.00  num_of_sem_filtered_clauses:            1
% 19.19/3.00  num_of_subtypes:                        0
% 19.19/3.00  monotx_restored_types:                  0
% 19.19/3.00  sat_num_of_epr_types:                   0
% 19.19/3.00  sat_num_of_non_cyclic_types:            0
% 19.19/3.00  sat_guarded_non_collapsed_types:        0
% 19.19/3.00  num_pure_diseq_elim:                    0
% 19.19/3.00  simp_replaced_by:                       0
% 19.19/3.00  res_preprocessed:                       142
% 19.19/3.00  prep_upred:                             0
% 19.19/3.00  prep_unflattend:                        57
% 19.19/3.00  smt_new_axioms:                         0
% 19.19/3.00  pred_elim_cands:                        6
% 19.19/3.00  pred_elim:                              2
% 19.19/3.00  pred_elim_cl:                           -1
% 19.19/3.00  pred_elim_cycles:                       7
% 19.19/3.00  merged_defs:                            8
% 19.19/3.00  merged_defs_ncl:                        0
% 19.19/3.00  bin_hyper_res:                          9
% 19.19/3.00  prep_cycles:                            4
% 19.19/3.00  pred_elim_time:                         0.026
% 19.19/3.00  splitting_time:                         0.
% 19.19/3.00  sem_filter_time:                        0.
% 19.19/3.00  monotx_time:                            0.
% 19.19/3.00  subtype_inf_time:                       0.
% 19.19/3.00  
% 19.19/3.00  ------ Problem properties
% 19.19/3.00  
% 19.19/3.00  clauses:                                28
% 19.19/3.00  conjectures:                            4
% 19.19/3.00  epr:                                    8
% 19.19/3.00  horn:                                   25
% 19.19/3.00  ground:                                 9
% 19.19/3.00  unary:                                  10
% 19.19/3.00  binary:                                 4
% 19.19/3.00  lits:                                   65
% 19.19/3.00  lits_eq:                                9
% 19.19/3.00  fd_pure:                                0
% 19.19/3.00  fd_pseudo:                              0
% 19.19/3.00  fd_cond:                                0
% 19.19/3.00  fd_pseudo_cond:                         2
% 19.19/3.00  ac_symbols:                             0
% 19.19/3.00  
% 19.19/3.00  ------ Propositional Solver
% 19.19/3.00  
% 19.19/3.00  prop_solver_calls:                      33
% 19.19/3.00  prop_fast_solver_calls:                 3071
% 19.19/3.00  smt_solver_calls:                       0
% 19.19/3.00  smt_fast_solver_calls:                  0
% 19.19/3.00  prop_num_of_clauses:                    19765
% 19.19/3.00  prop_preprocess_simplified:             40937
% 19.19/3.00  prop_fo_subsumed:                       186
% 19.19/3.00  prop_solver_time:                       0.
% 19.19/3.00  smt_solver_time:                        0.
% 19.19/3.00  smt_fast_solver_time:                   0.
% 19.19/3.00  prop_fast_solver_time:                  0.
% 19.19/3.00  prop_unsat_core_time:                   0.
% 19.19/3.00  
% 19.19/3.00  ------ QBF
% 19.19/3.00  
% 19.19/3.00  qbf_q_res:                              0
% 19.19/3.00  qbf_num_tautologies:                    0
% 19.19/3.00  qbf_prep_cycles:                        0
% 19.19/3.00  
% 19.19/3.00  ------ BMC1
% 19.19/3.00  
% 19.19/3.00  bmc1_current_bound:                     -1
% 19.19/3.00  bmc1_last_solved_bound:                 -1
% 19.19/3.00  bmc1_unsat_core_size:                   -1
% 19.19/3.00  bmc1_unsat_core_parents_size:           -1
% 19.19/3.00  bmc1_merge_next_fun:                    0
% 19.19/3.00  bmc1_unsat_core_clauses_time:           0.
% 19.19/3.00  
% 19.19/3.00  ------ Instantiation
% 19.19/3.00  
% 19.19/3.00  inst_num_of_clauses:                    5861
% 19.19/3.00  inst_num_in_passive:                    2042
% 19.19/3.00  inst_num_in_active:                     1705
% 19.19/3.00  inst_num_in_unprocessed:                2114
% 19.19/3.00  inst_num_of_loops:                      2160
% 19.19/3.00  inst_num_of_learning_restarts:          0
% 19.19/3.00  inst_num_moves_active_passive:          452
% 19.19/3.00  inst_lit_activity:                      0
% 19.19/3.00  inst_lit_activity_moves:                1
% 19.19/3.00  inst_num_tautologies:                   0
% 19.19/3.00  inst_num_prop_implied:                  0
% 19.19/3.00  inst_num_existing_simplified:           0
% 19.19/3.00  inst_num_eq_res_simplified:             0
% 19.19/3.00  inst_num_child_elim:                    0
% 19.19/3.00  inst_num_of_dismatching_blockings:      7223
% 19.19/3.00  inst_num_of_non_proper_insts:           8609
% 19.19/3.00  inst_num_of_duplicates:                 0
% 19.19/3.00  inst_inst_num_from_inst_to_res:         0
% 19.19/3.00  inst_dismatching_checking_time:         0.
% 19.19/3.00  
% 19.19/3.00  ------ Resolution
% 19.19/3.00  
% 19.19/3.00  res_num_of_clauses:                     0
% 19.19/3.00  res_num_in_passive:                     0
% 19.19/3.00  res_num_in_active:                      0
% 19.19/3.00  res_num_of_loops:                       146
% 19.19/3.00  res_forward_subset_subsumed:            1534
% 19.19/3.00  res_backward_subset_subsumed:           6
% 19.19/3.00  res_forward_subsumed:                   0
% 19.19/3.00  res_backward_subsumed:                  0
% 19.19/3.00  res_forward_subsumption_resolution:     0
% 19.19/3.00  res_backward_subsumption_resolution:    0
% 19.19/3.00  res_clause_to_clause_subsumption:       8792
% 19.19/3.00  res_orphan_elimination:                 0
% 19.19/3.00  res_tautology_del:                      629
% 19.19/3.00  res_num_eq_res_simplified:              0
% 19.19/3.00  res_num_sel_changes:                    0
% 19.19/3.00  res_moves_from_active_to_pass:          0
% 19.19/3.00  
% 19.19/3.00  ------ Superposition
% 19.19/3.00  
% 19.19/3.00  sup_time_total:                         0.
% 19.19/3.00  sup_time_generating:                    0.
% 19.19/3.00  sup_time_sim_full:                      0.
% 19.19/3.00  sup_time_sim_immed:                     0.
% 19.19/3.00  
% 19.19/3.00  sup_num_of_clauses:                     1647
% 19.19/3.00  sup_num_in_active:                      253
% 19.19/3.00  sup_num_in_passive:                     1394
% 19.19/3.00  sup_num_of_loops:                       430
% 19.19/3.00  sup_fw_superposition:                   1535
% 19.19/3.00  sup_bw_superposition:                   1683
% 19.19/3.00  sup_immediate_simplified:               1333
% 19.19/3.00  sup_given_eliminated:                   0
% 19.19/3.00  comparisons_done:                       0
% 19.19/3.00  comparisons_avoided:                    0
% 19.19/3.00  
% 19.19/3.00  ------ Simplifications
% 19.19/3.00  
% 19.19/3.00  
% 19.19/3.00  sim_fw_subset_subsumed:                 347
% 19.19/3.00  sim_bw_subset_subsumed:                 119
% 19.19/3.00  sim_fw_subsumed:                        173
% 19.19/3.00  sim_bw_subsumed:                        10
% 19.19/3.00  sim_fw_subsumption_res:                 0
% 19.19/3.00  sim_bw_subsumption_res:                 0
% 19.19/3.00  sim_tautology_del:                      17
% 19.19/3.00  sim_eq_tautology_del:                   60
% 19.19/3.00  sim_eq_res_simp:                        0
% 19.19/3.00  sim_fw_demodulated:                     16
% 19.19/3.00  sim_bw_demodulated:                     165
% 19.19/3.00  sim_light_normalised:                   905
% 19.19/3.00  sim_joinable_taut:                      0
% 19.19/3.00  sim_joinable_simp:                      0
% 19.19/3.00  sim_ac_normalised:                      0
% 19.19/3.00  sim_smt_subsumption:                    0
% 19.19/3.00  
%------------------------------------------------------------------------------
