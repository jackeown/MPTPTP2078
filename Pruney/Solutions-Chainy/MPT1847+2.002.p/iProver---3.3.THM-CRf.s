%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:24 EST 2020

% Result     : Theorem 47.80s
% Output     : CNFRefutation 47.80s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 552 expanded)
%              Number of clauses        :  116 ( 179 expanded)
%              Number of leaves         :   23 ( 150 expanded)
%              Depth                    :   18
%              Number of atoms          :  617 (2675 expanded)
%              Number of equality atoms :  269 ( 651 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( ( v1_tex_2(X1,X0)
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                 => v1_tex_2(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tex_2(X2,X0)
          & v1_tex_2(X1,X0)
          & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X2,X0) )
     => ( ~ v1_tex_2(sK4,X0)
        & v1_tex_2(X1,X0)
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
            & v1_tex_2(sK3,X0)
            & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
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
              ( ~ v1_tex_2(X2,sK2)
              & v1_tex_2(X1,sK2)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,sK2) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ~ v1_tex_2(sK4,sK2)
    & v1_tex_2(sK3,sK2)
    & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f56,f55,f54])).

fof(f89,plain,(
    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( ! [X2] :
            ( m1_subset_1(X2,X0)
           => r2_hidden(X2,X1) )
       => X0 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),X0) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | m1_subset_1(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK1(X0,X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK1(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ~ v1_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f90,plain,(
    v1_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_441,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2023,plain,
    ( X0 != X1
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_3666,plain,
    ( X0 != u1_struct_0(X1)
    | X0 = u1_struct_0(X2)
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_8300,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_3666])).

cnf(c_26734,plain,
    ( u1_struct_0(sK3) != u1_struct_0(X0)
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | u1_struct_0(sK4) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_8300])).

cnf(c_73826,plain,
    ( u1_struct_0(sK3) != u1_struct_0(sK3)
    | u1_struct_0(sK3) = u1_struct_0(sK4)
    | u1_struct_0(sK4) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_26734])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_958,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_30,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_265,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17,c_14])).

cnf(c_266,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_265])).

cnf(c_946,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_266])).

cnf(c_1265,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_946])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1280,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[status(thm)],[c_14,c_32])).

cnf(c_1281,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_3117,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1265,c_34,c_1281])).

cnf(c_3118,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3117])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_961,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3126,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3118,c_961])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1278,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK4) ),
    inference(resolution,[status(thm)],[c_14,c_31])).

cnf(c_1279,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_3965,plain,
    ( m1_pre_topc(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3126,c_34,c_1279])).

cnf(c_3966,plain,
    ( m1_pre_topc(X0,sK3) != iProver_top
    | m1_pre_topc(X0,sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3965])).

cnf(c_3974,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_3966])).

cnf(c_4132,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3974,c_34,c_1281])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_959,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X1,X0),X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_967,plain,
    ( X0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_970,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2380,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_970])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_972,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2379,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_967,c_972])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_78,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_100,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5500,plain,
    ( v1_xboole_0(X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2379,c_78,c_100])).

cnf(c_5501,plain,
    ( X0 = X1
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5500])).

cnf(c_5532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(sK0(X1,X0),X1) = iProver_top
    | X0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_5501])).

cnf(c_5533,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5532])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_969,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2869,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
    | r2_hidden(X2,u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_969])).

cnf(c_8475,plain,
    ( u1_struct_0(X0) = X1
    | m1_pre_topc(X0,X2) != iProver_top
    | r2_hidden(sK0(u1_struct_0(X0),X1),u1_struct_0(X2)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5533,c_2869])).

cnf(c_8,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_968,plain,
    ( X0 = X1
    | r2_hidden(sK0(X0,X1),X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_44971,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8475,c_968])).

cnf(c_46516,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_959,c_44971])).

cnf(c_72,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_46585,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46516,c_72])).

cnf(c_46586,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_46585])).

cnf(c_46605,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK3)
    | m1_pre_topc(sK4,sK3) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4132,c_46586])).

cnf(c_3090,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_30,c_961])).

cnf(c_3270,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3090,c_34,c_1281])).

cnf(c_3271,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3270])).

cnf(c_3278,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_946,c_3271])).

cnf(c_12865,plain,
    ( m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3278,c_34,c_1279])).

cnf(c_12866,plain,
    ( m1_pre_topc(X0,sK3) = iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_12865])).

cnf(c_12874,plain,
    ( m1_pre_topc(sK4,sK3) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_958,c_12866])).

cnf(c_1596,plain,
    ( X0 != X1
    | X0 = sK1(sK2,sK4)
    | sK1(sK2,sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_1895,plain,
    ( X0 = sK1(sK2,sK4)
    | X0 != u1_struct_0(sK4)
    | sK1(sK2,sK4) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_2232,plain,
    ( sK1(sK2,sK4) != u1_struct_0(sK4)
    | u1_struct_0(X0) = sK1(sK2,sK4)
    | u1_struct_0(X0) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_9772,plain,
    ( sK1(sK2,sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK3) = sK1(sK2,sK4)
    | u1_struct_0(sK3) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_1729,plain,
    ( X0 != X1
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_2797,plain,
    ( X0 != sK1(sK2,sK4)
    | X0 = u1_struct_0(sK2)
    | u1_struct_0(sK2) != sK1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1729])).

cnf(c_4118,plain,
    ( u1_struct_0(X0) != sK1(sK2,sK4)
    | u1_struct_0(X0) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != sK1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2797])).

cnf(c_6789,plain,
    ( u1_struct_0(sK3) != sK1(sK2,sK4)
    | u1_struct_0(sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != sK1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_4118])).

cnf(c_12,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4738,plain,
    ( ~ v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_445,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1300,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(u1_struct_0(X2),u1_struct_0(X3))
    | X0 != u1_struct_0(X2)
    | X1 != u1_struct_0(X3) ),
    inference(instantiation,[status(thm)],[c_445])).

cnf(c_1483,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK3)
    | X1 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_1731,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | X0 != u1_struct_0(sK3)
    | u1_struct_0(X1) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_3059,plain,
    ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(X0))
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_4737,plain,
    ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3059])).

cnf(c_950,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_955,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_954,plain,
    ( X0 = X1
    | v1_subset_1(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1764,plain,
    ( sK1(X0,X1) = u1_struct_0(X0)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_955,c_954])).

cnf(c_22,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_957,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_subset_1(sK1(X1,X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3901,plain,
    ( sK1(X0,X1) = u1_struct_0(X0)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1764,c_957])).

cnf(c_3906,plain,
    ( sK1(sK2,sK4) = u1_struct_0(sK2)
    | v1_tex_2(sK4,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_3901])).

cnf(c_23,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK1(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_956,plain,
    ( sK1(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1773,plain,
    ( sK1(sK2,sK4) = u1_struct_0(sK4)
    | v1_tex_2(sK4,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_956])).

cnf(c_28,negated_conjecture,
    ( ~ v1_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1253,plain,
    ( v1_tex_2(sK4,sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ l1_pre_topc(sK2)
    | sK1(sK2,sK4) = u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_3711,plain,
    ( sK1(sK2,sK4) = u1_struct_0(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_33,c_31,c_28,c_1253])).

cnf(c_3929,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK4)
    | v1_tex_2(sK4,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3906,c_3711])).

cnf(c_440,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2102,plain,
    ( u1_struct_0(X0) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_2778,plain,
    ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2102])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2015,plain,
    ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2279,plain,
    ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_2015])).

cnf(c_2234,plain,
    ( sK1(sK2,sK4) != u1_struct_0(sK4)
    | u1_struct_0(sK2) = sK1(sK2,sK4)
    | u1_struct_0(sK2) != u1_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_25,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_278,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_tex_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_25,c_19])).

cnf(c_279,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_1407,plain,
    ( ~ v1_tex_2(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_38,plain,
    ( v1_tex_2(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_29,negated_conjecture,
    ( v1_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_73826,c_46605,c_12874,c_9772,c_6789,c_4738,c_4737,c_3929,c_2778,c_2279,c_2234,c_1407,c_1279,c_1253,c_38,c_28,c_29,c_31,c_32,c_34,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 47.80/6.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 47.80/6.49  
% 47.80/6.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 47.80/6.49  
% 47.80/6.49  ------  iProver source info
% 47.80/6.49  
% 47.80/6.49  git: date: 2020-06-30 10:37:57 +0100
% 47.80/6.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 47.80/6.49  git: non_committed_changes: false
% 47.80/6.49  git: last_make_outside_of_git: false
% 47.80/6.49  
% 47.80/6.49  ------ 
% 47.80/6.49  
% 47.80/6.49  ------ Input Options
% 47.80/6.49  
% 47.80/6.49  --out_options                           all
% 47.80/6.49  --tptp_safe_out                         true
% 47.80/6.49  --problem_path                          ""
% 47.80/6.49  --include_path                          ""
% 47.80/6.49  --clausifier                            res/vclausify_rel
% 47.80/6.49  --clausifier_options                    --mode clausify
% 47.80/6.49  --stdin                                 false
% 47.80/6.49  --stats_out                             sel
% 47.80/6.49  
% 47.80/6.49  ------ General Options
% 47.80/6.49  
% 47.80/6.49  --fof                                   false
% 47.80/6.49  --time_out_real                         604.99
% 47.80/6.49  --time_out_virtual                      -1.
% 47.80/6.49  --symbol_type_check                     false
% 47.80/6.49  --clausify_out                          false
% 47.80/6.49  --sig_cnt_out                           false
% 47.80/6.49  --trig_cnt_out                          false
% 47.80/6.49  --trig_cnt_out_tolerance                1.
% 47.80/6.49  --trig_cnt_out_sk_spl                   false
% 47.80/6.49  --abstr_cl_out                          false
% 47.80/6.49  
% 47.80/6.49  ------ Global Options
% 47.80/6.49  
% 47.80/6.49  --schedule                              none
% 47.80/6.49  --add_important_lit                     false
% 47.80/6.49  --prop_solver_per_cl                    1000
% 47.80/6.49  --min_unsat_core                        false
% 47.80/6.49  --soft_assumptions                      false
% 47.80/6.49  --soft_lemma_size                       3
% 47.80/6.49  --prop_impl_unit_size                   0
% 47.80/6.49  --prop_impl_unit                        []
% 47.80/6.49  --share_sel_clauses                     true
% 47.80/6.49  --reset_solvers                         false
% 47.80/6.49  --bc_imp_inh                            [conj_cone]
% 47.80/6.49  --conj_cone_tolerance                   3.
% 47.80/6.49  --extra_neg_conj                        none
% 47.80/6.49  --large_theory_mode                     true
% 47.80/6.49  --prolific_symb_bound                   200
% 47.80/6.49  --lt_threshold                          2000
% 47.80/6.49  --clause_weak_htbl                      true
% 47.80/6.49  --gc_record_bc_elim                     false
% 47.80/6.49  
% 47.80/6.49  ------ Preprocessing Options
% 47.80/6.49  
% 47.80/6.49  --preprocessing_flag                    true
% 47.80/6.49  --time_out_prep_mult                    0.1
% 47.80/6.49  --splitting_mode                        input
% 47.80/6.49  --splitting_grd                         true
% 47.80/6.49  --splitting_cvd                         false
% 47.80/6.49  --splitting_cvd_svl                     false
% 47.80/6.49  --splitting_nvd                         32
% 47.80/6.49  --sub_typing                            true
% 47.80/6.49  --prep_gs_sim                           false
% 47.80/6.49  --prep_unflatten                        true
% 47.80/6.49  --prep_res_sim                          true
% 47.80/6.49  --prep_upred                            true
% 47.80/6.49  --prep_sem_filter                       exhaustive
% 47.80/6.49  --prep_sem_filter_out                   false
% 47.80/6.49  --pred_elim                             false
% 47.80/6.49  --res_sim_input                         true
% 47.80/6.49  --eq_ax_congr_red                       true
% 47.80/6.49  --pure_diseq_elim                       true
% 47.80/6.49  --brand_transform                       false
% 47.80/6.49  --non_eq_to_eq                          false
% 47.80/6.49  --prep_def_merge                        true
% 47.80/6.49  --prep_def_merge_prop_impl              false
% 47.80/6.49  --prep_def_merge_mbd                    true
% 47.80/6.49  --prep_def_merge_tr_red                 false
% 47.80/6.49  --prep_def_merge_tr_cl                  false
% 47.80/6.49  --smt_preprocessing                     true
% 47.80/6.49  --smt_ac_axioms                         fast
% 47.80/6.49  --preprocessed_out                      false
% 47.80/6.49  --preprocessed_stats                    false
% 47.80/6.49  
% 47.80/6.49  ------ Abstraction refinement Options
% 47.80/6.49  
% 47.80/6.49  --abstr_ref                             []
% 47.80/6.49  --abstr_ref_prep                        false
% 47.80/6.49  --abstr_ref_until_sat                   false
% 47.80/6.49  --abstr_ref_sig_restrict                funpre
% 47.80/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.80/6.49  --abstr_ref_under                       []
% 47.80/6.49  
% 47.80/6.49  ------ SAT Options
% 47.80/6.49  
% 47.80/6.49  --sat_mode                              false
% 47.80/6.49  --sat_fm_restart_options                ""
% 47.80/6.49  --sat_gr_def                            false
% 47.80/6.49  --sat_epr_types                         true
% 47.80/6.49  --sat_non_cyclic_types                  false
% 47.80/6.49  --sat_finite_models                     false
% 47.80/6.49  --sat_fm_lemmas                         false
% 47.80/6.49  --sat_fm_prep                           false
% 47.80/6.49  --sat_fm_uc_incr                        true
% 47.80/6.49  --sat_out_model                         small
% 47.80/6.49  --sat_out_clauses                       false
% 47.80/6.49  
% 47.80/6.49  ------ QBF Options
% 47.80/6.49  
% 47.80/6.49  --qbf_mode                              false
% 47.80/6.49  --qbf_elim_univ                         false
% 47.80/6.49  --qbf_dom_inst                          none
% 47.80/6.49  --qbf_dom_pre_inst                      false
% 47.80/6.49  --qbf_sk_in                             false
% 47.80/6.49  --qbf_pred_elim                         true
% 47.80/6.49  --qbf_split                             512
% 47.80/6.49  
% 47.80/6.49  ------ BMC1 Options
% 47.80/6.49  
% 47.80/6.49  --bmc1_incremental                      false
% 47.80/6.49  --bmc1_axioms                           reachable_all
% 47.80/6.49  --bmc1_min_bound                        0
% 47.80/6.49  --bmc1_max_bound                        -1
% 47.80/6.49  --bmc1_max_bound_default                -1
% 47.80/6.49  --bmc1_symbol_reachability              true
% 47.80/6.49  --bmc1_property_lemmas                  false
% 47.80/6.49  --bmc1_k_induction                      false
% 47.80/6.49  --bmc1_non_equiv_states                 false
% 47.80/6.49  --bmc1_deadlock                         false
% 47.80/6.49  --bmc1_ucm                              false
% 47.80/6.49  --bmc1_add_unsat_core                   none
% 47.80/6.49  --bmc1_unsat_core_children              false
% 47.80/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.80/6.49  --bmc1_out_stat                         full
% 47.80/6.49  --bmc1_ground_init                      false
% 47.80/6.49  --bmc1_pre_inst_next_state              false
% 47.80/6.49  --bmc1_pre_inst_state                   false
% 47.80/6.49  --bmc1_pre_inst_reach_state             false
% 47.80/6.49  --bmc1_out_unsat_core                   false
% 47.80/6.49  --bmc1_aig_witness_out                  false
% 47.80/6.49  --bmc1_verbose                          false
% 47.80/6.49  --bmc1_dump_clauses_tptp                false
% 47.80/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.80/6.49  --bmc1_dump_file                        -
% 47.80/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.80/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.80/6.49  --bmc1_ucm_extend_mode                  1
% 47.80/6.49  --bmc1_ucm_init_mode                    2
% 47.80/6.49  --bmc1_ucm_cone_mode                    none
% 47.80/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.80/6.49  --bmc1_ucm_relax_model                  4
% 47.80/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.80/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.80/6.49  --bmc1_ucm_layered_model                none
% 47.80/6.49  --bmc1_ucm_max_lemma_size               10
% 47.80/6.49  
% 47.80/6.49  ------ AIG Options
% 47.80/6.49  
% 47.80/6.49  --aig_mode                              false
% 47.80/6.49  
% 47.80/6.49  ------ Instantiation Options
% 47.80/6.49  
% 47.80/6.49  --instantiation_flag                    true
% 47.80/6.49  --inst_sos_flag                         false
% 47.80/6.49  --inst_sos_phase                        true
% 47.80/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.80/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.80/6.49  --inst_lit_sel_side                     num_symb
% 47.80/6.49  --inst_solver_per_active                1400
% 47.80/6.49  --inst_solver_calls_frac                1.
% 47.80/6.49  --inst_passive_queue_type               priority_queues
% 47.80/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.80/6.49  --inst_passive_queues_freq              [25;2]
% 47.80/6.49  --inst_dismatching                      true
% 47.80/6.49  --inst_eager_unprocessed_to_passive     true
% 47.80/6.49  --inst_prop_sim_given                   true
% 47.80/6.49  --inst_prop_sim_new                     false
% 47.80/6.49  --inst_subs_new                         false
% 47.80/6.49  --inst_eq_res_simp                      false
% 47.80/6.49  --inst_subs_given                       false
% 47.80/6.49  --inst_orphan_elimination               true
% 47.80/6.49  --inst_learning_loop_flag               true
% 47.80/6.49  --inst_learning_start                   3000
% 47.80/6.49  --inst_learning_factor                  2
% 47.80/6.49  --inst_start_prop_sim_after_learn       3
% 47.80/6.49  --inst_sel_renew                        solver
% 47.80/6.49  --inst_lit_activity_flag                true
% 47.80/6.49  --inst_restr_to_given                   false
% 47.80/6.49  --inst_activity_threshold               500
% 47.80/6.49  --inst_out_proof                        true
% 47.80/6.49  
% 47.80/6.49  ------ Resolution Options
% 47.80/6.49  
% 47.80/6.49  --resolution_flag                       true
% 47.80/6.49  --res_lit_sel                           adaptive
% 47.80/6.49  --res_lit_sel_side                      none
% 47.80/6.49  --res_ordering                          kbo
% 47.80/6.49  --res_to_prop_solver                    active
% 47.80/6.49  --res_prop_simpl_new                    false
% 47.80/6.49  --res_prop_simpl_given                  true
% 47.80/6.49  --res_passive_queue_type                priority_queues
% 47.80/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.80/6.49  --res_passive_queues_freq               [15;5]
% 47.80/6.49  --res_forward_subs                      full
% 47.80/6.49  --res_backward_subs                     full
% 47.80/6.49  --res_forward_subs_resolution           true
% 47.80/6.49  --res_backward_subs_resolution          true
% 47.80/6.49  --res_orphan_elimination                true
% 47.80/6.49  --res_time_limit                        2.
% 47.80/6.49  --res_out_proof                         true
% 47.80/6.49  
% 47.80/6.49  ------ Superposition Options
% 47.80/6.49  
% 47.80/6.49  --superposition_flag                    true
% 47.80/6.49  --sup_passive_queue_type                priority_queues
% 47.80/6.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.80/6.49  --sup_passive_queues_freq               [1;4]
% 47.80/6.49  --demod_completeness_check              fast
% 47.80/6.49  --demod_use_ground                      true
% 47.80/6.49  --sup_to_prop_solver                    passive
% 47.80/6.49  --sup_prop_simpl_new                    true
% 47.80/6.49  --sup_prop_simpl_given                  true
% 47.80/6.49  --sup_fun_splitting                     false
% 47.80/6.49  --sup_smt_interval                      50000
% 47.80/6.49  
% 47.80/6.49  ------ Superposition Simplification Setup
% 47.80/6.49  
% 47.80/6.49  --sup_indices_passive                   []
% 47.80/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.80/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_full_bw                           [BwDemod]
% 47.80/6.49  --sup_immed_triv                        [TrivRules]
% 47.80/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.80/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_immed_bw_main                     []
% 47.80/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.80/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.80/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.80/6.49  
% 47.80/6.49  ------ Combination Options
% 47.80/6.49  
% 47.80/6.49  --comb_res_mult                         3
% 47.80/6.49  --comb_sup_mult                         2
% 47.80/6.49  --comb_inst_mult                        10
% 47.80/6.49  
% 47.80/6.49  ------ Debug Options
% 47.80/6.49  
% 47.80/6.49  --dbg_backtrace                         false
% 47.80/6.49  --dbg_dump_prop_clauses                 false
% 47.80/6.49  --dbg_dump_prop_clauses_file            -
% 47.80/6.49  --dbg_out_stat                          false
% 47.80/6.49  ------ Parsing...
% 47.80/6.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 47.80/6.49  
% 47.80/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 47.80/6.49  
% 47.80/6.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 47.80/6.49  
% 47.80/6.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 47.80/6.49  ------ Proving...
% 47.80/6.49  ------ Problem Properties 
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  clauses                                 33
% 47.80/6.49  conjectures                             6
% 47.80/6.49  EPR                                     13
% 47.80/6.49  Horn                                    27
% 47.80/6.49  unary                                   8
% 47.80/6.49  binary                                  3
% 47.80/6.49  lits                                    85
% 47.80/6.49  lits eq                                 7
% 47.80/6.49  fd_pure                                 0
% 47.80/6.49  fd_pseudo                               0
% 47.80/6.49  fd_cond                                 0
% 47.80/6.49  fd_pseudo_cond                          4
% 47.80/6.49  AC symbols                              0
% 47.80/6.49  
% 47.80/6.49  ------ Input Options Time Limit: Unbounded
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  ------ 
% 47.80/6.49  Current options:
% 47.80/6.49  ------ 
% 47.80/6.49  
% 47.80/6.49  ------ Input Options
% 47.80/6.49  
% 47.80/6.49  --out_options                           all
% 47.80/6.49  --tptp_safe_out                         true
% 47.80/6.49  --problem_path                          ""
% 47.80/6.49  --include_path                          ""
% 47.80/6.49  --clausifier                            res/vclausify_rel
% 47.80/6.49  --clausifier_options                    --mode clausify
% 47.80/6.49  --stdin                                 false
% 47.80/6.49  --stats_out                             sel
% 47.80/6.49  
% 47.80/6.49  ------ General Options
% 47.80/6.49  
% 47.80/6.49  --fof                                   false
% 47.80/6.49  --time_out_real                         604.99
% 47.80/6.49  --time_out_virtual                      -1.
% 47.80/6.49  --symbol_type_check                     false
% 47.80/6.49  --clausify_out                          false
% 47.80/6.49  --sig_cnt_out                           false
% 47.80/6.49  --trig_cnt_out                          false
% 47.80/6.49  --trig_cnt_out_tolerance                1.
% 47.80/6.49  --trig_cnt_out_sk_spl                   false
% 47.80/6.49  --abstr_cl_out                          false
% 47.80/6.49  
% 47.80/6.49  ------ Global Options
% 47.80/6.49  
% 47.80/6.49  --schedule                              none
% 47.80/6.49  --add_important_lit                     false
% 47.80/6.49  --prop_solver_per_cl                    1000
% 47.80/6.49  --min_unsat_core                        false
% 47.80/6.49  --soft_assumptions                      false
% 47.80/6.49  --soft_lemma_size                       3
% 47.80/6.49  --prop_impl_unit_size                   0
% 47.80/6.49  --prop_impl_unit                        []
% 47.80/6.49  --share_sel_clauses                     true
% 47.80/6.49  --reset_solvers                         false
% 47.80/6.49  --bc_imp_inh                            [conj_cone]
% 47.80/6.49  --conj_cone_tolerance                   3.
% 47.80/6.49  --extra_neg_conj                        none
% 47.80/6.49  --large_theory_mode                     true
% 47.80/6.49  --prolific_symb_bound                   200
% 47.80/6.49  --lt_threshold                          2000
% 47.80/6.49  --clause_weak_htbl                      true
% 47.80/6.49  --gc_record_bc_elim                     false
% 47.80/6.49  
% 47.80/6.49  ------ Preprocessing Options
% 47.80/6.49  
% 47.80/6.49  --preprocessing_flag                    true
% 47.80/6.49  --time_out_prep_mult                    0.1
% 47.80/6.49  --splitting_mode                        input
% 47.80/6.49  --splitting_grd                         true
% 47.80/6.49  --splitting_cvd                         false
% 47.80/6.49  --splitting_cvd_svl                     false
% 47.80/6.49  --splitting_nvd                         32
% 47.80/6.49  --sub_typing                            true
% 47.80/6.49  --prep_gs_sim                           false
% 47.80/6.49  --prep_unflatten                        true
% 47.80/6.49  --prep_res_sim                          true
% 47.80/6.49  --prep_upred                            true
% 47.80/6.49  --prep_sem_filter                       exhaustive
% 47.80/6.49  --prep_sem_filter_out                   false
% 47.80/6.49  --pred_elim                             false
% 47.80/6.49  --res_sim_input                         true
% 47.80/6.49  --eq_ax_congr_red                       true
% 47.80/6.49  --pure_diseq_elim                       true
% 47.80/6.49  --brand_transform                       false
% 47.80/6.49  --non_eq_to_eq                          false
% 47.80/6.49  --prep_def_merge                        true
% 47.80/6.49  --prep_def_merge_prop_impl              false
% 47.80/6.49  --prep_def_merge_mbd                    true
% 47.80/6.49  --prep_def_merge_tr_red                 false
% 47.80/6.49  --prep_def_merge_tr_cl                  false
% 47.80/6.49  --smt_preprocessing                     true
% 47.80/6.49  --smt_ac_axioms                         fast
% 47.80/6.49  --preprocessed_out                      false
% 47.80/6.49  --preprocessed_stats                    false
% 47.80/6.49  
% 47.80/6.49  ------ Abstraction refinement Options
% 47.80/6.49  
% 47.80/6.49  --abstr_ref                             []
% 47.80/6.49  --abstr_ref_prep                        false
% 47.80/6.49  --abstr_ref_until_sat                   false
% 47.80/6.49  --abstr_ref_sig_restrict                funpre
% 47.80/6.49  --abstr_ref_af_restrict_to_split_sk     false
% 47.80/6.49  --abstr_ref_under                       []
% 47.80/6.49  
% 47.80/6.49  ------ SAT Options
% 47.80/6.49  
% 47.80/6.49  --sat_mode                              false
% 47.80/6.49  --sat_fm_restart_options                ""
% 47.80/6.49  --sat_gr_def                            false
% 47.80/6.49  --sat_epr_types                         true
% 47.80/6.49  --sat_non_cyclic_types                  false
% 47.80/6.49  --sat_finite_models                     false
% 47.80/6.49  --sat_fm_lemmas                         false
% 47.80/6.49  --sat_fm_prep                           false
% 47.80/6.49  --sat_fm_uc_incr                        true
% 47.80/6.49  --sat_out_model                         small
% 47.80/6.49  --sat_out_clauses                       false
% 47.80/6.49  
% 47.80/6.49  ------ QBF Options
% 47.80/6.49  
% 47.80/6.49  --qbf_mode                              false
% 47.80/6.49  --qbf_elim_univ                         false
% 47.80/6.49  --qbf_dom_inst                          none
% 47.80/6.49  --qbf_dom_pre_inst                      false
% 47.80/6.49  --qbf_sk_in                             false
% 47.80/6.49  --qbf_pred_elim                         true
% 47.80/6.49  --qbf_split                             512
% 47.80/6.49  
% 47.80/6.49  ------ BMC1 Options
% 47.80/6.49  
% 47.80/6.49  --bmc1_incremental                      false
% 47.80/6.49  --bmc1_axioms                           reachable_all
% 47.80/6.49  --bmc1_min_bound                        0
% 47.80/6.49  --bmc1_max_bound                        -1
% 47.80/6.49  --bmc1_max_bound_default                -1
% 47.80/6.49  --bmc1_symbol_reachability              true
% 47.80/6.49  --bmc1_property_lemmas                  false
% 47.80/6.49  --bmc1_k_induction                      false
% 47.80/6.49  --bmc1_non_equiv_states                 false
% 47.80/6.49  --bmc1_deadlock                         false
% 47.80/6.49  --bmc1_ucm                              false
% 47.80/6.49  --bmc1_add_unsat_core                   none
% 47.80/6.49  --bmc1_unsat_core_children              false
% 47.80/6.49  --bmc1_unsat_core_extrapolate_axioms    false
% 47.80/6.49  --bmc1_out_stat                         full
% 47.80/6.49  --bmc1_ground_init                      false
% 47.80/6.49  --bmc1_pre_inst_next_state              false
% 47.80/6.49  --bmc1_pre_inst_state                   false
% 47.80/6.49  --bmc1_pre_inst_reach_state             false
% 47.80/6.49  --bmc1_out_unsat_core                   false
% 47.80/6.49  --bmc1_aig_witness_out                  false
% 47.80/6.49  --bmc1_verbose                          false
% 47.80/6.49  --bmc1_dump_clauses_tptp                false
% 47.80/6.49  --bmc1_dump_unsat_core_tptp             false
% 47.80/6.49  --bmc1_dump_file                        -
% 47.80/6.49  --bmc1_ucm_expand_uc_limit              128
% 47.80/6.49  --bmc1_ucm_n_expand_iterations          6
% 47.80/6.49  --bmc1_ucm_extend_mode                  1
% 47.80/6.49  --bmc1_ucm_init_mode                    2
% 47.80/6.49  --bmc1_ucm_cone_mode                    none
% 47.80/6.49  --bmc1_ucm_reduced_relation_type        0
% 47.80/6.49  --bmc1_ucm_relax_model                  4
% 47.80/6.49  --bmc1_ucm_full_tr_after_sat            true
% 47.80/6.49  --bmc1_ucm_expand_neg_assumptions       false
% 47.80/6.49  --bmc1_ucm_layered_model                none
% 47.80/6.49  --bmc1_ucm_max_lemma_size               10
% 47.80/6.49  
% 47.80/6.49  ------ AIG Options
% 47.80/6.49  
% 47.80/6.49  --aig_mode                              false
% 47.80/6.49  
% 47.80/6.49  ------ Instantiation Options
% 47.80/6.49  
% 47.80/6.49  --instantiation_flag                    true
% 47.80/6.49  --inst_sos_flag                         false
% 47.80/6.49  --inst_sos_phase                        true
% 47.80/6.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 47.80/6.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 47.80/6.49  --inst_lit_sel_side                     num_symb
% 47.80/6.49  --inst_solver_per_active                1400
% 47.80/6.49  --inst_solver_calls_frac                1.
% 47.80/6.49  --inst_passive_queue_type               priority_queues
% 47.80/6.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 47.80/6.49  --inst_passive_queues_freq              [25;2]
% 47.80/6.49  --inst_dismatching                      true
% 47.80/6.49  --inst_eager_unprocessed_to_passive     true
% 47.80/6.49  --inst_prop_sim_given                   true
% 47.80/6.49  --inst_prop_sim_new                     false
% 47.80/6.49  --inst_subs_new                         false
% 47.80/6.49  --inst_eq_res_simp                      false
% 47.80/6.49  --inst_subs_given                       false
% 47.80/6.49  --inst_orphan_elimination               true
% 47.80/6.49  --inst_learning_loop_flag               true
% 47.80/6.49  --inst_learning_start                   3000
% 47.80/6.49  --inst_learning_factor                  2
% 47.80/6.49  --inst_start_prop_sim_after_learn       3
% 47.80/6.49  --inst_sel_renew                        solver
% 47.80/6.49  --inst_lit_activity_flag                true
% 47.80/6.49  --inst_restr_to_given                   false
% 47.80/6.49  --inst_activity_threshold               500
% 47.80/6.49  --inst_out_proof                        true
% 47.80/6.49  
% 47.80/6.49  ------ Resolution Options
% 47.80/6.49  
% 47.80/6.49  --resolution_flag                       true
% 47.80/6.49  --res_lit_sel                           adaptive
% 47.80/6.49  --res_lit_sel_side                      none
% 47.80/6.49  --res_ordering                          kbo
% 47.80/6.49  --res_to_prop_solver                    active
% 47.80/6.49  --res_prop_simpl_new                    false
% 47.80/6.49  --res_prop_simpl_given                  true
% 47.80/6.49  --res_passive_queue_type                priority_queues
% 47.80/6.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 47.80/6.49  --res_passive_queues_freq               [15;5]
% 47.80/6.49  --res_forward_subs                      full
% 47.80/6.49  --res_backward_subs                     full
% 47.80/6.49  --res_forward_subs_resolution           true
% 47.80/6.49  --res_backward_subs_resolution          true
% 47.80/6.49  --res_orphan_elimination                true
% 47.80/6.49  --res_time_limit                        2.
% 47.80/6.49  --res_out_proof                         true
% 47.80/6.49  
% 47.80/6.49  ------ Superposition Options
% 47.80/6.49  
% 47.80/6.49  --superposition_flag                    true
% 47.80/6.49  --sup_passive_queue_type                priority_queues
% 47.80/6.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 47.80/6.49  --sup_passive_queues_freq               [1;4]
% 47.80/6.49  --demod_completeness_check              fast
% 47.80/6.49  --demod_use_ground                      true
% 47.80/6.49  --sup_to_prop_solver                    passive
% 47.80/6.49  --sup_prop_simpl_new                    true
% 47.80/6.49  --sup_prop_simpl_given                  true
% 47.80/6.49  --sup_fun_splitting                     false
% 47.80/6.49  --sup_smt_interval                      50000
% 47.80/6.49  
% 47.80/6.49  ------ Superposition Simplification Setup
% 47.80/6.49  
% 47.80/6.49  --sup_indices_passive                   []
% 47.80/6.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 47.80/6.49  --sup_full_triv                         [TrivRules;PropSubs]
% 47.80/6.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_full_bw                           [BwDemod]
% 47.80/6.49  --sup_immed_triv                        [TrivRules]
% 47.80/6.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 47.80/6.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_immed_bw_main                     []
% 47.80/6.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.80/6.49  --sup_input_triv                        [Unflattening;TrivRules]
% 47.80/6.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 47.80/6.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 47.80/6.49  
% 47.80/6.49  ------ Combination Options
% 47.80/6.49  
% 47.80/6.49  --comb_res_mult                         3
% 47.80/6.49  --comb_sup_mult                         2
% 47.80/6.49  --comb_inst_mult                        10
% 47.80/6.49  
% 47.80/6.49  ------ Debug Options
% 47.80/6.49  
% 47.80/6.49  --dbg_backtrace                         false
% 47.80/6.49  --dbg_dump_prop_clauses                 false
% 47.80/6.49  --dbg_dump_prop_clauses_file            -
% 47.80/6.49  --dbg_out_stat                          false
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  ------ Proving...
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  % SZS status Theorem for theBenchmark.p
% 47.80/6.49  
% 47.80/6.49  % SZS output start CNFRefutation for theBenchmark.p
% 47.80/6.49  
% 47.80/6.49  fof(f16,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f37,plain,(
% 47.80/6.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f16])).
% 47.80/6.49  
% 47.80/6.49  fof(f78,plain,(
% 47.80/6.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f37])).
% 47.80/6.49  
% 47.80/6.49  fof(f20,conjecture,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f21,negated_conjecture,(
% 47.80/6.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 47.80/6.49    inference(negated_conjecture,[],[f20])).
% 47.80/6.49  
% 47.80/6.49  fof(f43,plain,(
% 47.80/6.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f21])).
% 47.80/6.49  
% 47.80/6.49  fof(f44,plain,(
% 47.80/6.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 47.80/6.49    inference(flattening,[],[f43])).
% 47.80/6.49  
% 47.80/6.49  fof(f56,plain,(
% 47.80/6.49    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK4,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK4,X0))) )),
% 47.80/6.49    introduced(choice_axiom,[])).
% 47.80/6.49  
% 47.80/6.49  fof(f55,plain,(
% 47.80/6.49    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK3,X0) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK3,X0))) )),
% 47.80/6.49    introduced(choice_axiom,[])).
% 47.80/6.49  
% 47.80/6.49  fof(f54,plain,(
% 47.80/6.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK2) & v1_tex_2(X1,sK2) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 47.80/6.49    introduced(choice_axiom,[])).
% 47.80/6.49  
% 47.80/6.49  fof(f57,plain,(
% 47.80/6.49    ((~v1_tex_2(sK4,sK2) & v1_tex_2(sK3,sK2) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) & m1_pre_topc(sK4,sK2)) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 47.80/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f56,f55,f54])).
% 47.80/6.49  
% 47.80/6.49  fof(f89,plain,(
% 47.80/6.49    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  fof(f13,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f34,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f13])).
% 47.80/6.49  
% 47.80/6.49  fof(f48,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(nnf_transformation,[],[f34])).
% 47.80/6.49  
% 47.80/6.49  fof(f74,plain,(
% 47.80/6.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f48])).
% 47.80/6.49  
% 47.80/6.49  fof(f11,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f32,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f11])).
% 47.80/6.49  
% 47.80/6.49  fof(f72,plain,(
% 47.80/6.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f32])).
% 47.80/6.49  
% 47.80/6.49  fof(f86,plain,(
% 47.80/6.49    l1_pre_topc(sK2)),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  fof(f87,plain,(
% 47.80/6.49    m1_pre_topc(sK3,sK2)),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  fof(f12,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f33,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f12])).
% 47.80/6.49  
% 47.80/6.49  fof(f73,plain,(
% 47.80/6.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f33])).
% 47.80/6.49  
% 47.80/6.49  fof(f88,plain,(
% 47.80/6.49    m1_pre_topc(sK4,sK2)),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  fof(f15,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f36,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f15])).
% 47.80/6.49  
% 47.80/6.49  fof(f77,plain,(
% 47.80/6.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f36])).
% 47.80/6.49  
% 47.80/6.49  fof(f6,axiom,(
% 47.80/6.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (! [X2] : (m1_subset_1(X2,X0) => r2_hidden(X2,X1)) => X0 = X1))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f27,plain,(
% 47.80/6.49    ! [X0,X1] : ((X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(ennf_transformation,[],[f6])).
% 47.80/6.49  
% 47.80/6.49  fof(f28,plain,(
% 47.80/6.49    ! [X0,X1] : (X0 = X1 | ? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(flattening,[],[f27])).
% 47.80/6.49  
% 47.80/6.49  fof(f46,plain,(
% 47.80/6.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)))),
% 47.80/6.49    introduced(choice_axiom,[])).
% 47.80/6.49  
% 47.80/6.49  fof(f47,plain,(
% 47.80/6.49    ! [X0,X1] : (X0 = X1 | (~r2_hidden(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f46])).
% 47.80/6.49  
% 47.80/6.49  fof(f66,plain,(
% 47.80/6.49    ( ! [X0,X1] : (X0 = X1 | m1_subset_1(sK0(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.80/6.49    inference(cnf_transformation,[],[f47])).
% 47.80/6.49  
% 47.80/6.49  fof(f3,axiom,(
% 47.80/6.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f25,plain,(
% 47.80/6.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 47.80/6.49    inference(ennf_transformation,[],[f3])).
% 47.80/6.49  
% 47.80/6.49  fof(f45,plain,(
% 47.80/6.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 47.80/6.49    inference(nnf_transformation,[],[f25])).
% 47.80/6.49  
% 47.80/6.49  fof(f60,plain,(
% 47.80/6.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f45])).
% 47.80/6.49  
% 47.80/6.49  fof(f62,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f45])).
% 47.80/6.49  
% 47.80/6.49  fof(f7,axiom,(
% 47.80/6.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f29,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f7])).
% 47.80/6.49  
% 47.80/6.49  fof(f68,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f29])).
% 47.80/6.49  
% 47.80/6.49  fof(f1,axiom,(
% 47.80/6.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f23,plain,(
% 47.80/6.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f1])).
% 47.80/6.49  
% 47.80/6.49  fof(f58,plain,(
% 47.80/6.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f23])).
% 47.80/6.49  
% 47.80/6.49  fof(f5,axiom,(
% 47.80/6.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f26,plain,(
% 47.80/6.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(ennf_transformation,[],[f5])).
% 47.80/6.49  
% 47.80/6.49  fof(f65,plain,(
% 47.80/6.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.80/6.49    inference(cnf_transformation,[],[f26])).
% 47.80/6.49  
% 47.80/6.49  fof(f67,plain,(
% 47.80/6.49    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.80/6.49    inference(cnf_transformation,[],[f47])).
% 47.80/6.49  
% 47.80/6.49  fof(f9,axiom,(
% 47.80/6.49    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f70,plain,(
% 47.80/6.49    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f9])).
% 47.80/6.49  
% 47.80/6.49  fof(f18,axiom,(
% 47.80/6.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f40,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(ennf_transformation,[],[f18])).
% 47.80/6.49  
% 47.80/6.49  fof(f41,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(flattening,[],[f40])).
% 47.80/6.49  
% 47.80/6.49  fof(f49,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(nnf_transformation,[],[f41])).
% 47.80/6.49  
% 47.80/6.49  fof(f50,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(rectify,[],[f49])).
% 47.80/6.49  
% 47.80/6.49  fof(f51,plain,(
% 47.80/6.49    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 47.80/6.49    introduced(choice_axiom,[])).
% 47.80/6.49  
% 47.80/6.49  fof(f52,plain,(
% 47.80/6.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK1(X0,X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 47.80/6.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f50,f51])).
% 47.80/6.49  
% 47.80/6.49  fof(f81,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f52])).
% 47.80/6.49  
% 47.80/6.49  fof(f19,axiom,(
% 47.80/6.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f42,plain,(
% 47.80/6.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(ennf_transformation,[],[f19])).
% 47.80/6.49  
% 47.80/6.49  fof(f53,plain,(
% 47.80/6.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 47.80/6.49    inference(nnf_transformation,[],[f42])).
% 47.80/6.49  
% 47.80/6.49  fof(f85,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 47.80/6.49    inference(cnf_transformation,[],[f53])).
% 47.80/6.49  
% 47.80/6.49  fof(f83,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f52])).
% 47.80/6.49  
% 47.80/6.49  fof(f82,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK1(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f52])).
% 47.80/6.49  
% 47.80/6.49  fof(f91,plain,(
% 47.80/6.49    ~v1_tex_2(sK4,sK2)),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  fof(f4,axiom,(
% 47.80/6.49    ! [X0] : k2_subset_1(X0) = X0),
% 47.80/6.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 47.80/6.49  
% 47.80/6.49  fof(f64,plain,(
% 47.80/6.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 47.80/6.49    inference(cnf_transformation,[],[f4])).
% 47.80/6.49  
% 47.80/6.49  fof(f80,plain,(
% 47.80/6.49    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(cnf_transformation,[],[f52])).
% 47.80/6.49  
% 47.80/6.49  fof(f92,plain,(
% 47.80/6.49    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 47.80/6.49    inference(equality_resolution,[],[f80])).
% 47.80/6.49  
% 47.80/6.49  fof(f90,plain,(
% 47.80/6.49    v1_tex_2(sK3,sK2)),
% 47.80/6.49    inference(cnf_transformation,[],[f57])).
% 47.80/6.49  
% 47.80/6.49  cnf(c_441,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2023,plain,
% 47.80/6.49      ( X0 != X1 | X0 = u1_struct_0(X2) | u1_struct_0(X2) != X1 ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_441]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3666,plain,
% 47.80/6.49      ( X0 != u1_struct_0(X1)
% 47.80/6.49      | X0 = u1_struct_0(X2)
% 47.80/6.49      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2023]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_8300,plain,
% 47.80/6.49      ( u1_struct_0(X0) != u1_struct_0(X1)
% 47.80/6.49      | u1_struct_0(X2) != u1_struct_0(X1)
% 47.80/6.49      | u1_struct_0(X0) = u1_struct_0(X2) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_3666]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_26734,plain,
% 47.80/6.49      ( u1_struct_0(sK3) != u1_struct_0(X0)
% 47.80/6.49      | u1_struct_0(sK3) = u1_struct_0(sK4)
% 47.80/6.49      | u1_struct_0(sK4) != u1_struct_0(X0) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_8300]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_73826,plain,
% 47.80/6.49      ( u1_struct_0(sK3) != u1_struct_0(sK3)
% 47.80/6.49      | u1_struct_0(sK3) = u1_struct_0(sK4)
% 47.80/6.49      | u1_struct_0(sK4) != u1_struct_0(sK3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_26734]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_20,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f78]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_958,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X0) = iProver_top
% 47.80/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_30,negated_conjecture,
% 47.80/6.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
% 47.80/6.49      inference(cnf_transformation,[],[f89]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_17,plain,
% 47.80/6.49      ( ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X0)
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f74]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_14,plain,
% 47.80/6.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f72]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_265,plain,
% 47.80/6.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_17,c_14]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_266,plain,
% 47.80/6.49      ( ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_265]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_946,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_266]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1265,plain,
% 47.80/6.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) != iProver_top
% 47.80/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_30,c_946]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_33,negated_conjecture,
% 47.80/6.49      ( l1_pre_topc(sK2) ),
% 47.80/6.49      inference(cnf_transformation,[],[f86]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_34,plain,
% 47.80/6.49      ( l1_pre_topc(sK2) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_32,negated_conjecture,
% 47.80/6.49      ( m1_pre_topc(sK3,sK2) ),
% 47.80/6.49      inference(cnf_transformation,[],[f87]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1280,plain,
% 47.80/6.49      ( l1_pre_topc(sK3) | ~ l1_pre_topc(sK2) ),
% 47.80/6.49      inference(resolution,[status(thm)],[c_14,c_32]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1281,plain,
% 47.80/6.49      ( l1_pre_topc(sK3) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_1280]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3117,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_1265,c_34,c_1281]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3118,plain,
% 47.80/6.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) != iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_3117]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_15,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f73]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_961,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3126,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK4) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK4) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_3118,c_961]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_31,negated_conjecture,
% 47.80/6.49      ( m1_pre_topc(sK4,sK2) ),
% 47.80/6.49      inference(cnf_transformation,[],[f88]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1278,plain,
% 47.80/6.49      ( ~ l1_pre_topc(sK2) | l1_pre_topc(sK4) ),
% 47.80/6.49      inference(resolution,[status(thm)],[c_14,c_31]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1279,plain,
% 47.80/6.49      ( l1_pre_topc(sK2) != iProver_top
% 47.80/6.49      | l1_pre_topc(sK4) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3965,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK4) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) != iProver_top ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_3126,c_34,c_1279]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3966,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK4) = iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_3965]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3974,plain,
% 47.80/6.49      ( m1_pre_topc(sK3,sK4) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_958,c_3966]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_4132,plain,
% 47.80/6.49      ( m1_pre_topc(sK3,sK4) = iProver_top ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_3974,c_34,c_1281]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_19,plain,
% 47.80/6.49      ( ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f77]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_959,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_9,plain,
% 47.80/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.80/6.49      | m1_subset_1(sK0(X1,X0),X1)
% 47.80/6.49      | X1 = X0 ),
% 47.80/6.49      inference(cnf_transformation,[],[f66]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_967,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 47.80/6.49      | m1_subset_1(sK0(X0,X1),X0) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_5,plain,
% 47.80/6.49      ( r2_hidden(X0,X1) | ~ m1_subset_1(X0,X1) | v1_xboole_0(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f60]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_970,plain,
% 47.80/6.49      ( r2_hidden(X0,X1) = iProver_top
% 47.80/6.49      | m1_subset_1(X0,X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2380,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top
% 47.80/6.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) = iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_967,c_970]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3,plain,
% 47.80/6.49      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f62]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_972,plain,
% 47.80/6.49      ( m1_subset_1(X0,X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(X0) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2379,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(sK0(X1,X0)) = iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_967,c_972]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_10,plain,
% 47.80/6.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.80/6.49      | ~ v1_xboole_0(X1)
% 47.80/6.49      | v1_xboole_0(X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f68]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_78,plain,
% 47.80/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(X0) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_0,plain,
% 47.80/6.49      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 47.80/6.49      inference(cnf_transformation,[],[f58]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_100,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | v1_xboole_0(X1) != iProver_top
% 47.80/6.49      | v1_xboole_0(X0) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_5500,plain,
% 47.80/6.49      ( v1_xboole_0(X1) != iProver_top
% 47.80/6.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | X0 = X1 ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_2379,c_78,c_100]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_5501,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | v1_xboole_0(X1) != iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_5500]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_5532,plain,
% 47.80/6.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 47.80/6.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top
% 47.80/6.49      | X0 = X1 ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_2380,c_5501]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_5533,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | r2_hidden(sK0(X1,X0),X1) = iProver_top
% 47.80/6.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_5532]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_7,plain,
% 47.80/6.49      ( ~ r2_hidden(X0,X1)
% 47.80/6.49      | r2_hidden(X0,X2)
% 47.80/6.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 47.80/6.49      inference(cnf_transformation,[],[f65]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_969,plain,
% 47.80/6.49      ( r2_hidden(X0,X1) != iProver_top
% 47.80/6.49      | r2_hidden(X0,X2) = iProver_top
% 47.80/6.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2869,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | r2_hidden(X2,u1_struct_0(X0)) != iProver_top
% 47.80/6.49      | r2_hidden(X2,u1_struct_0(X1)) = iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_959,c_969]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_8475,plain,
% 47.80/6.49      ( u1_struct_0(X0) = X1
% 47.80/6.49      | m1_pre_topc(X0,X2) != iProver_top
% 47.80/6.49      | r2_hidden(sK0(u1_struct_0(X0),X1),u1_struct_0(X2)) = iProver_top
% 47.80/6.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.80/6.49      | l1_pre_topc(X2) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_5533,c_2869]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_8,plain,
% 47.80/6.49      ( ~ r2_hidden(sK0(X0,X1),X1)
% 47.80/6.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 47.80/6.49      | X0 = X1 ),
% 47.80/6.49      inference(cnf_transformation,[],[f67]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_968,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | r2_hidden(sK0(X0,X1),X1) != iProver_top
% 47.80/6.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_44971,plain,
% 47.80/6.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_8475,c_968]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_46516,plain,
% 47.80/6.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top
% 47.80/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_959,c_44971]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_72,plain,
% 47.80/6.49      ( m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top
% 47.80/6.49      | l1_pre_topc(X0) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_46585,plain,
% 47.80/6.49      ( l1_pre_topc(X1) != iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_46516,c_72]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_46586,plain,
% 47.80/6.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_46585]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_46605,plain,
% 47.80/6.49      ( u1_struct_0(sK4) = u1_struct_0(sK3)
% 47.80/6.49      | m1_pre_topc(sK4,sK3) != iProver_top
% 47.80/6.49      | l1_pre_topc(sK4) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_4132,c_46586]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3090,plain,
% 47.80/6.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK3) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_30,c_961]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3270,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_3090,c_34,c_1281]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3271,plain,
% 47.80/6.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) = iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_3270]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3278,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK4) != iProver_top
% 47.80/6.49      | l1_pre_topc(sK4) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_946,c_3271]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_12865,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK4) != iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK3) = iProver_top ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_3278,c_34,c_1279]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_12866,plain,
% 47.80/6.49      ( m1_pre_topc(X0,sK3) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,sK4) != iProver_top ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_12865]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_12874,plain,
% 47.80/6.49      ( m1_pre_topc(sK4,sK3) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK4) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_958,c_12866]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1596,plain,
% 47.80/6.49      ( X0 != X1 | X0 = sK1(sK2,sK4) | sK1(sK2,sK4) != X1 ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_441]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1895,plain,
% 47.80/6.49      ( X0 = sK1(sK2,sK4)
% 47.80/6.49      | X0 != u1_struct_0(sK4)
% 47.80/6.49      | sK1(sK2,sK4) != u1_struct_0(sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1596]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2232,plain,
% 47.80/6.49      ( sK1(sK2,sK4) != u1_struct_0(sK4)
% 47.80/6.49      | u1_struct_0(X0) = sK1(sK2,sK4)
% 47.80/6.49      | u1_struct_0(X0) != u1_struct_0(sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1895]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_9772,plain,
% 47.80/6.49      ( sK1(sK2,sK4) != u1_struct_0(sK4)
% 47.80/6.49      | u1_struct_0(sK3) = sK1(sK2,sK4)
% 47.80/6.49      | u1_struct_0(sK3) != u1_struct_0(sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2232]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1729,plain,
% 47.80/6.49      ( X0 != X1 | X0 = u1_struct_0(sK2) | u1_struct_0(sK2) != X1 ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_441]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2797,plain,
% 47.80/6.49      ( X0 != sK1(sK2,sK4)
% 47.80/6.49      | X0 = u1_struct_0(sK2)
% 47.80/6.49      | u1_struct_0(sK2) != sK1(sK2,sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1729]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_4118,plain,
% 47.80/6.49      ( u1_struct_0(X0) != sK1(sK2,sK4)
% 47.80/6.49      | u1_struct_0(X0) = u1_struct_0(sK2)
% 47.80/6.49      | u1_struct_0(sK2) != sK1(sK2,sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2797]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_6789,plain,
% 47.80/6.49      ( u1_struct_0(sK3) != sK1(sK2,sK4)
% 47.80/6.49      | u1_struct_0(sK3) = u1_struct_0(sK2)
% 47.80/6.49      | u1_struct_0(sK2) != sK1(sK2,sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_4118]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_12,plain,
% 47.80/6.49      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f70]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_4738,plain,
% 47.80/6.49      ( ~ v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_12]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_445,plain,
% 47.80/6.49      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 47.80/6.49      theory(equality) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1300,plain,
% 47.80/6.49      ( v1_subset_1(X0,X1)
% 47.80/6.49      | ~ v1_subset_1(u1_struct_0(X2),u1_struct_0(X3))
% 47.80/6.49      | X0 != u1_struct_0(X2)
% 47.80/6.49      | X1 != u1_struct_0(X3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_445]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1483,plain,
% 47.80/6.49      ( v1_subset_1(X0,X1)
% 47.80/6.49      | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 47.80/6.49      | X0 != u1_struct_0(sK3)
% 47.80/6.49      | X1 != u1_struct_0(sK2) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1300]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1731,plain,
% 47.80/6.49      ( v1_subset_1(X0,u1_struct_0(X1))
% 47.80/6.49      | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 47.80/6.49      | X0 != u1_struct_0(sK3)
% 47.80/6.49      | u1_struct_0(X1) != u1_struct_0(sK2) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1483]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3059,plain,
% 47.80/6.49      ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 47.80/6.49      | v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(X0))
% 47.80/6.49      | u1_struct_0(X0) != u1_struct_0(sK2)
% 47.80/6.49      | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_1731]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_4737,plain,
% 47.80/6.49      ( ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 47.80/6.49      | v1_subset_1(k2_subset_1(u1_struct_0(sK3)),u1_struct_0(sK3))
% 47.80/6.49      | u1_struct_0(sK3) != u1_struct_0(sK2)
% 47.80/6.49      | k2_subset_1(u1_struct_0(sK3)) != u1_struct_0(sK3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_3059]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_950,plain,
% 47.80/6.49      ( m1_pre_topc(sK4,sK2) = iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_24,plain,
% 47.80/6.49      ( v1_tex_2(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f81]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_955,plain,
% 47.80/6.49      ( v1_tex_2(X0,X1) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | m1_subset_1(sK1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_26,plain,
% 47.80/6.49      ( v1_subset_1(X0,X1)
% 47.80/6.49      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 47.80/6.49      | X1 = X0 ),
% 47.80/6.49      inference(cnf_transformation,[],[f85]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_954,plain,
% 47.80/6.49      ( X0 = X1
% 47.80/6.49      | v1_subset_1(X1,X0) = iProver_top
% 47.80/6.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1764,plain,
% 47.80/6.49      ( sK1(X0,X1) = u1_struct_0(X0)
% 47.80/6.49      | v1_tex_2(X1,X0) = iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | v1_subset_1(sK1(X0,X1),u1_struct_0(X0)) = iProver_top
% 47.80/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_955,c_954]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_22,plain,
% 47.80/6.49      ( v1_tex_2(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | ~ v1_subset_1(sK1(X1,X0),u1_struct_0(X1))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f83]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_957,plain,
% 47.80/6.49      ( v1_tex_2(X0,X1) = iProver_top
% 47.80/6.49      | m1_pre_topc(X0,X1) != iProver_top
% 47.80/6.49      | v1_subset_1(sK1(X1,X0),u1_struct_0(X1)) != iProver_top
% 47.80/6.49      | l1_pre_topc(X1) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3901,plain,
% 47.80/6.49      ( sK1(X0,X1) = u1_struct_0(X0)
% 47.80/6.49      | v1_tex_2(X1,X0) = iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.80/6.49      inference(forward_subsumption_resolution,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_1764,c_957]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3906,plain,
% 47.80/6.49      ( sK1(sK2,sK4) = u1_struct_0(sK2)
% 47.80/6.49      | v1_tex_2(sK4,sK2) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_950,c_3901]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_23,plain,
% 47.80/6.49      ( v1_tex_2(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | ~ l1_pre_topc(X1)
% 47.80/6.49      | sK1(X1,X0) = u1_struct_0(X0) ),
% 47.80/6.49      inference(cnf_transformation,[],[f82]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_956,plain,
% 47.80/6.49      ( sK1(X0,X1) = u1_struct_0(X1)
% 47.80/6.49      | v1_tex_2(X1,X0) = iProver_top
% 47.80/6.49      | m1_pre_topc(X1,X0) != iProver_top
% 47.80/6.49      | l1_pre_topc(X0) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1773,plain,
% 47.80/6.49      ( sK1(sK2,sK4) = u1_struct_0(sK4)
% 47.80/6.49      | v1_tex_2(sK4,sK2) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 47.80/6.49      inference(superposition,[status(thm)],[c_950,c_956]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_28,negated_conjecture,
% 47.80/6.49      ( ~ v1_tex_2(sK4,sK2) ),
% 47.80/6.49      inference(cnf_transformation,[],[f91]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1253,plain,
% 47.80/6.49      ( v1_tex_2(sK4,sK2)
% 47.80/6.49      | ~ m1_pre_topc(sK4,sK2)
% 47.80/6.49      | ~ l1_pre_topc(sK2)
% 47.80/6.49      | sK1(sK2,sK4) = u1_struct_0(sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_23]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3711,plain,
% 47.80/6.49      ( sK1(sK2,sK4) = u1_struct_0(sK4) ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_1773,c_33,c_31,c_28,c_1253]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_3929,plain,
% 47.80/6.49      ( u1_struct_0(sK2) = u1_struct_0(sK4)
% 47.80/6.49      | v1_tex_2(sK4,sK2) = iProver_top
% 47.80/6.49      | l1_pre_topc(sK2) != iProver_top ),
% 47.80/6.49      inference(light_normalisation,[status(thm)],[c_3906,c_3711]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_440,plain,( X0 = X0 ),theory(equality) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2102,plain,
% 47.80/6.49      ( u1_struct_0(X0) = u1_struct_0(X0) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_440]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2778,plain,
% 47.80/6.49      ( u1_struct_0(sK3) = u1_struct_0(sK3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2102]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_6,plain,
% 47.80/6.49      ( k2_subset_1(X0) = X0 ),
% 47.80/6.49      inference(cnf_transformation,[],[f64]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2015,plain,
% 47.80/6.49      ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_6]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2279,plain,
% 47.80/6.49      ( k2_subset_1(u1_struct_0(sK3)) = u1_struct_0(sK3) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2015]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_2234,plain,
% 47.80/6.49      ( sK1(sK2,sK4) != u1_struct_0(sK4)
% 47.80/6.49      | u1_struct_0(sK2) = sK1(sK2,sK4)
% 47.80/6.49      | u1_struct_0(sK2) != u1_struct_0(sK4) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_2232]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_25,plain,
% 47.80/6.49      ( ~ v1_tex_2(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 47.80/6.49      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(cnf_transformation,[],[f92]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_278,plain,
% 47.80/6.49      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | ~ v1_tex_2(X0,X1)
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(global_propositional_subsumption,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_25,c_19]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_279,plain,
% 47.80/6.49      ( ~ v1_tex_2(X0,X1)
% 47.80/6.49      | ~ m1_pre_topc(X0,X1)
% 47.80/6.49      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 47.80/6.49      | ~ l1_pre_topc(X1) ),
% 47.80/6.49      inference(renaming,[status(thm)],[c_278]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_1407,plain,
% 47.80/6.49      ( ~ v1_tex_2(sK3,sK2)
% 47.80/6.49      | ~ m1_pre_topc(sK3,sK2)
% 47.80/6.49      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK2))
% 47.80/6.49      | ~ l1_pre_topc(sK2) ),
% 47.80/6.49      inference(instantiation,[status(thm)],[c_279]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_38,plain,
% 47.80/6.49      ( v1_tex_2(sK4,sK2) != iProver_top ),
% 47.80/6.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(c_29,negated_conjecture,
% 47.80/6.49      ( v1_tex_2(sK3,sK2) ),
% 47.80/6.49      inference(cnf_transformation,[],[f90]) ).
% 47.80/6.49  
% 47.80/6.49  cnf(contradiction,plain,
% 47.80/6.49      ( $false ),
% 47.80/6.49      inference(minisat,
% 47.80/6.49                [status(thm)],
% 47.80/6.49                [c_73826,c_46605,c_12874,c_9772,c_6789,c_4738,c_4737,
% 47.80/6.49                 c_3929,c_2778,c_2279,c_2234,c_1407,c_1279,c_1253,c_38,
% 47.80/6.49                 c_28,c_29,c_31,c_32,c_34,c_33]) ).
% 47.80/6.49  
% 47.80/6.49  
% 47.80/6.49  % SZS output end CNFRefutation for theBenchmark.p
% 47.80/6.49  
% 47.80/6.49  ------                               Statistics
% 47.80/6.49  
% 47.80/6.49  ------ Selected
% 47.80/6.49  
% 47.80/6.49  total_time:                             5.901
% 47.80/6.49  
%------------------------------------------------------------------------------
