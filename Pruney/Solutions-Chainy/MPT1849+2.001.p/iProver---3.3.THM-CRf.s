%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:28 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  197 (2302 expanded)
%              Number of clauses        :  128 ( 744 expanded)
%              Number of leaves         :   19 ( 494 expanded)
%              Depth                    :   22
%              Number of atoms          :  577 (8421 expanded)
%              Number of equality atoms :  319 (2592 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
     => ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & m1_pre_topc(sK2,X0)
        & ~ v1_tex_2(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,sK1)
          & ~ v1_tex_2(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v1_tex_2(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f52,f51])).

fof(f83,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f59,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X0] :
      ( k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    ~ v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_21,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3105,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3108,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5351,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3105,c_3108])).

cnf(c_13,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_3111,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3114,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3712,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_3114])).

cnf(c_12109,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5351,c_3712])).

cnf(c_12110,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12109])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3095,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3117,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4469,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3712,c_3117])).

cnf(c_3360,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3361,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3360])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3113,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3568,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_3113])).

cnf(c_8623,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4469,c_3361,c_3568,c_3712])).

cnf(c_8624,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8623])).

cnf(c_8631,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_3095,c_8624])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3109,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9007,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8631,c_3109])).

cnf(c_9405,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9007])).

cnf(c_33,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_75,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_77,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_9844,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9405,c_33,c_77])).

cnf(c_11,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_351,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_11,c_8])).

cnf(c_3093,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_351])).

cnf(c_4180,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3712,c_3093])).

cnf(c_4649,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(superposition,[status(thm)],[c_3095,c_4180])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X0)
    | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3116,plain,
    ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5925,plain,
    ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4649,c_3116])).

cnf(c_5967,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5925,c_4649])).

cnf(c_57,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_59,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_57])).

cnf(c_20,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_60,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_62,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_6328,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5967,c_33,c_59,c_62])).

cnf(c_6329,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6328])).

cnf(c_9851,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9844,c_6329])).

cnf(c_12128,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_12110,c_9851])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_63,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_65,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_63])).

cnf(c_9887,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_9851])).

cnf(c_13450,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12128,c_33,c_59,c_65,c_9887])).

cnf(c_13451,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13450])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3118,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3131,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3118,c_3])).

cnf(c_13456,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13451,c_3131])).

cnf(c_13468,plain,
    ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK1))) = u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_13456,c_9844])).

cnf(c_3452,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_3095,c_3093])).

cnf(c_5924,plain,
    ( k1_pre_topc(X0,k2_struct_0(sK1)) = sK1
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3452,c_3116])).

cnf(c_5978,plain,
    ( k1_pre_topc(X0,u1_struct_0(sK1)) = sK1
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5924,c_3452])).

cnf(c_14040,plain,
    ( k1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1)) = sK1
    | m1_pre_topc(sK1,k1_pre_topc(sK1,u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1))) != iProver_top
    | v1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13468,c_5978])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_35,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3097,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3102,plain,
    ( sK0(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5810,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2)
    | v1_tex_2(sK2,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3102])).

cnf(c_31,negated_conjecture,
    ( ~ v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_707,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_708,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_707])).

cnf(c_6118,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5810,c_32,c_30,c_708])).

cnf(c_25,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3101,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6122,plain,
    ( v1_tex_2(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_3101])).

cnf(c_34,plain,
    ( v1_tex_2(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6341,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6122,c_33,c_34,c_35])).

cnf(c_27,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3099,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6347,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6341,c_3099])).

cnf(c_23,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3103,plain,
    ( v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) != iProver_top
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_6121,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_tex_2(sK2,sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6118,c_3103])).

cnf(c_6753,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6347,c_33,c_34,c_35,c_6121])).

cnf(c_3107,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6828,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6753,c_3107])).

cnf(c_6955,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6828])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3112,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5326,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3107,c_3112])).

cnf(c_5485,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_5326])).

cnf(c_5559,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5485,c_33])).

cnf(c_5565,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5559,c_3117])).

cnf(c_3106,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5023,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3106])).

cnf(c_5436,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_5437,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5436])).

cnf(c_5645,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5565,c_33,c_5023,c_5437,c_5485])).

cnf(c_5654,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5645,c_3109])).

cnf(c_5699,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
    | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_5654])).

cnf(c_3692,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3697,plain,
    ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3692])).

cnf(c_4147,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_4148,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4147])).

cnf(c_4150,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4148])).

cnf(c_12353,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5699,c_33,c_35,c_3697,c_4150])).

cnf(c_12355,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_12353,c_6753])).

cnf(c_4189,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3097,c_3112])).

cnf(c_4235,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4189,c_33,c_35,c_4150])).

cnf(c_4651,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    inference(superposition,[status(thm)],[c_4235,c_4180])).

cnf(c_5928,plain,
    ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4651,c_3116])).

cnf(c_5934,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5928,c_4651])).

cnf(c_11821,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5934,c_33,c_5023])).

cnf(c_11822,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11821])).

cnf(c_11827,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11822,c_6753])).

cnf(c_12357,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12355,c_11827])).

cnf(c_12373,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12357])).

cnf(c_29,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_6768,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(demodulation,[status(thm)],[c_6753,c_29])).

cnf(c_13470,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_13456,c_6768])).

cnf(c_14193,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14040,c_33,c_35,c_6955,c_12373,c_13470])).

cnf(c_14198,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_14193,c_3131])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.98  
% 3.65/0.98  ------  iProver source info
% 3.65/0.98  
% 3.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.98  git: non_committed_changes: false
% 3.65/0.98  git: last_make_outside_of_git: false
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options
% 3.65/0.98  
% 3.65/0.98  --out_options                           all
% 3.65/0.98  --tptp_safe_out                         true
% 3.65/0.98  --problem_path                          ""
% 3.65/0.98  --include_path                          ""
% 3.65/0.98  --clausifier                            res/vclausify_rel
% 3.65/0.98  --clausifier_options                    --mode clausify
% 3.65/0.98  --stdin                                 false
% 3.65/0.98  --stats_out                             all
% 3.65/0.98  
% 3.65/0.98  ------ General Options
% 3.65/0.98  
% 3.65/0.98  --fof                                   false
% 3.65/0.98  --time_out_real                         305.
% 3.65/0.98  --time_out_virtual                      -1.
% 3.65/0.98  --symbol_type_check                     false
% 3.65/0.98  --clausify_out                          false
% 3.65/0.98  --sig_cnt_out                           false
% 3.65/0.98  --trig_cnt_out                          false
% 3.65/0.98  --trig_cnt_out_tolerance                1.
% 3.65/0.98  --trig_cnt_out_sk_spl                   false
% 3.65/0.98  --abstr_cl_out                          false
% 3.65/0.98  
% 3.65/0.98  ------ Global Options
% 3.65/0.98  
% 3.65/0.98  --schedule                              default
% 3.65/0.98  --add_important_lit                     false
% 3.65/0.98  --prop_solver_per_cl                    1000
% 3.65/0.98  --min_unsat_core                        false
% 3.65/0.98  --soft_assumptions                      false
% 3.65/0.98  --soft_lemma_size                       3
% 3.65/0.98  --prop_impl_unit_size                   0
% 3.65/0.98  --prop_impl_unit                        []
% 3.65/0.98  --share_sel_clauses                     true
% 3.65/0.98  --reset_solvers                         false
% 3.65/0.98  --bc_imp_inh                            [conj_cone]
% 3.65/0.98  --conj_cone_tolerance                   3.
% 3.65/0.98  --extra_neg_conj                        none
% 3.65/0.98  --large_theory_mode                     true
% 3.65/0.98  --prolific_symb_bound                   200
% 3.65/0.98  --lt_threshold                          2000
% 3.65/0.98  --clause_weak_htbl                      true
% 3.65/0.98  --gc_record_bc_elim                     false
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing Options
% 3.65/0.98  
% 3.65/0.98  --preprocessing_flag                    true
% 3.65/0.98  --time_out_prep_mult                    0.1
% 3.65/0.98  --splitting_mode                        input
% 3.65/0.98  --splitting_grd                         true
% 3.65/0.98  --splitting_cvd                         false
% 3.65/0.98  --splitting_cvd_svl                     false
% 3.65/0.98  --splitting_nvd                         32
% 3.65/0.98  --sub_typing                            true
% 3.65/0.98  --prep_gs_sim                           true
% 3.65/0.98  --prep_unflatten                        true
% 3.65/0.98  --prep_res_sim                          true
% 3.65/0.98  --prep_upred                            true
% 3.65/0.98  --prep_sem_filter                       exhaustive
% 3.65/0.98  --prep_sem_filter_out                   false
% 3.65/0.98  --pred_elim                             true
% 3.65/0.98  --res_sim_input                         true
% 3.65/0.98  --eq_ax_congr_red                       true
% 3.65/0.98  --pure_diseq_elim                       true
% 3.65/0.98  --brand_transform                       false
% 3.65/0.98  --non_eq_to_eq                          false
% 3.65/0.98  --prep_def_merge                        true
% 3.65/0.98  --prep_def_merge_prop_impl              false
% 3.65/0.98  --prep_def_merge_mbd                    true
% 3.65/0.98  --prep_def_merge_tr_red                 false
% 3.65/0.98  --prep_def_merge_tr_cl                  false
% 3.65/0.98  --smt_preprocessing                     true
% 3.65/0.98  --smt_ac_axioms                         fast
% 3.65/0.98  --preprocessed_out                      false
% 3.65/0.98  --preprocessed_stats                    false
% 3.65/0.98  
% 3.65/0.98  ------ Abstraction refinement Options
% 3.65/0.98  
% 3.65/0.98  --abstr_ref                             []
% 3.65/0.98  --abstr_ref_prep                        false
% 3.65/0.98  --abstr_ref_until_sat                   false
% 3.65/0.98  --abstr_ref_sig_restrict                funpre
% 3.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.98  --abstr_ref_under                       []
% 3.65/0.98  
% 3.65/0.98  ------ SAT Options
% 3.65/0.98  
% 3.65/0.98  --sat_mode                              false
% 3.65/0.98  --sat_fm_restart_options                ""
% 3.65/0.98  --sat_gr_def                            false
% 3.65/0.98  --sat_epr_types                         true
% 3.65/0.98  --sat_non_cyclic_types                  false
% 3.65/0.98  --sat_finite_models                     false
% 3.65/0.98  --sat_fm_lemmas                         false
% 3.65/0.98  --sat_fm_prep                           false
% 3.65/0.98  --sat_fm_uc_incr                        true
% 3.65/0.98  --sat_out_model                         small
% 3.65/0.98  --sat_out_clauses                       false
% 3.65/0.98  
% 3.65/0.98  ------ QBF Options
% 3.65/0.98  
% 3.65/0.98  --qbf_mode                              false
% 3.65/0.98  --qbf_elim_univ                         false
% 3.65/0.98  --qbf_dom_inst                          none
% 3.65/0.98  --qbf_dom_pre_inst                      false
% 3.65/0.98  --qbf_sk_in                             false
% 3.65/0.98  --qbf_pred_elim                         true
% 3.65/0.98  --qbf_split                             512
% 3.65/0.98  
% 3.65/0.98  ------ BMC1 Options
% 3.65/0.98  
% 3.65/0.98  --bmc1_incremental                      false
% 3.65/0.98  --bmc1_axioms                           reachable_all
% 3.65/0.98  --bmc1_min_bound                        0
% 3.65/0.98  --bmc1_max_bound                        -1
% 3.65/0.98  --bmc1_max_bound_default                -1
% 3.65/0.98  --bmc1_symbol_reachability              true
% 3.65/0.98  --bmc1_property_lemmas                  false
% 3.65/0.98  --bmc1_k_induction                      false
% 3.65/0.98  --bmc1_non_equiv_states                 false
% 3.65/0.98  --bmc1_deadlock                         false
% 3.65/0.98  --bmc1_ucm                              false
% 3.65/0.98  --bmc1_add_unsat_core                   none
% 3.65/0.98  --bmc1_unsat_core_children              false
% 3.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.98  --bmc1_out_stat                         full
% 3.65/0.98  --bmc1_ground_init                      false
% 3.65/0.98  --bmc1_pre_inst_next_state              false
% 3.65/0.98  --bmc1_pre_inst_state                   false
% 3.65/0.98  --bmc1_pre_inst_reach_state             false
% 3.65/0.98  --bmc1_out_unsat_core                   false
% 3.65/0.98  --bmc1_aig_witness_out                  false
% 3.65/0.98  --bmc1_verbose                          false
% 3.65/0.98  --bmc1_dump_clauses_tptp                false
% 3.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.98  --bmc1_dump_file                        -
% 3.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.98  --bmc1_ucm_extend_mode                  1
% 3.65/0.98  --bmc1_ucm_init_mode                    2
% 3.65/0.98  --bmc1_ucm_cone_mode                    none
% 3.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.98  --bmc1_ucm_relax_model                  4
% 3.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.98  --bmc1_ucm_layered_model                none
% 3.65/0.98  --bmc1_ucm_max_lemma_size               10
% 3.65/0.98  
% 3.65/0.98  ------ AIG Options
% 3.65/0.98  
% 3.65/0.98  --aig_mode                              false
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation Options
% 3.65/0.98  
% 3.65/0.98  --instantiation_flag                    true
% 3.65/0.98  --inst_sos_flag                         false
% 3.65/0.98  --inst_sos_phase                        true
% 3.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel_side                     num_symb
% 3.65/0.98  --inst_solver_per_active                1400
% 3.65/0.98  --inst_solver_calls_frac                1.
% 3.65/0.98  --inst_passive_queue_type               priority_queues
% 3.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.98  --inst_passive_queues_freq              [25;2]
% 3.65/0.98  --inst_dismatching                      true
% 3.65/0.98  --inst_eager_unprocessed_to_passive     true
% 3.65/0.98  --inst_prop_sim_given                   true
% 3.65/0.98  --inst_prop_sim_new                     false
% 3.65/0.98  --inst_subs_new                         false
% 3.65/0.98  --inst_eq_res_simp                      false
% 3.65/0.98  --inst_subs_given                       false
% 3.65/0.98  --inst_orphan_elimination               true
% 3.65/0.98  --inst_learning_loop_flag               true
% 3.65/0.98  --inst_learning_start                   3000
% 3.65/0.98  --inst_learning_factor                  2
% 3.65/0.98  --inst_start_prop_sim_after_learn       3
% 3.65/0.98  --inst_sel_renew                        solver
% 3.65/0.98  --inst_lit_activity_flag                true
% 3.65/0.98  --inst_restr_to_given                   false
% 3.65/0.98  --inst_activity_threshold               500
% 3.65/0.98  --inst_out_proof                        true
% 3.65/0.98  
% 3.65/0.98  ------ Resolution Options
% 3.65/0.98  
% 3.65/0.98  --resolution_flag                       true
% 3.65/0.98  --res_lit_sel                           adaptive
% 3.65/0.98  --res_lit_sel_side                      none
% 3.65/0.98  --res_ordering                          kbo
% 3.65/0.98  --res_to_prop_solver                    active
% 3.65/0.98  --res_prop_simpl_new                    false
% 3.65/0.98  --res_prop_simpl_given                  true
% 3.65/0.98  --res_passive_queue_type                priority_queues
% 3.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  ------ Parsing...
% 3.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.98  ------ Proving...
% 3.65/0.98  ------ Problem Properties 
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  clauses                                 30
% 3.65/0.98  conjectures                             4
% 3.65/0.98  EPR                                     7
% 3.65/0.98  Horn                                    27
% 3.65/0.98  unary                                   7
% 3.65/0.98  binary                                  6
% 3.65/0.98  lits                                    79
% 3.65/0.98  lits eq                                 13
% 3.65/0.98  fd_pure                                 0
% 3.65/0.98  fd_pseudo                               0
% 3.65/0.98  fd_cond                                 0
% 3.65/0.98  fd_pseudo_cond                          4
% 3.65/0.98  AC symbols                              0
% 3.65/0.98  
% 3.65/0.98  ------ Schedule dynamic 5 is on 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ 
% 3.65/0.98  Current options:
% 3.65/0.98  ------ 
% 3.65/0.98  
% 3.65/0.98  ------ Input Options
% 3.65/0.98  
% 3.65/0.98  --out_options                           all
% 3.65/0.98  --tptp_safe_out                         true
% 3.65/0.98  --problem_path                          ""
% 3.65/0.98  --include_path                          ""
% 3.65/0.98  --clausifier                            res/vclausify_rel
% 3.65/0.98  --clausifier_options                    --mode clausify
% 3.65/0.98  --stdin                                 false
% 3.65/0.98  --stats_out                             all
% 3.65/0.98  
% 3.65/0.98  ------ General Options
% 3.65/0.98  
% 3.65/0.98  --fof                                   false
% 3.65/0.98  --time_out_real                         305.
% 3.65/0.98  --time_out_virtual                      -1.
% 3.65/0.98  --symbol_type_check                     false
% 3.65/0.98  --clausify_out                          false
% 3.65/0.98  --sig_cnt_out                           false
% 3.65/0.98  --trig_cnt_out                          false
% 3.65/0.98  --trig_cnt_out_tolerance                1.
% 3.65/0.98  --trig_cnt_out_sk_spl                   false
% 3.65/0.98  --abstr_cl_out                          false
% 3.65/0.98  
% 3.65/0.98  ------ Global Options
% 3.65/0.98  
% 3.65/0.98  --schedule                              default
% 3.65/0.98  --add_important_lit                     false
% 3.65/0.98  --prop_solver_per_cl                    1000
% 3.65/0.98  --min_unsat_core                        false
% 3.65/0.98  --soft_assumptions                      false
% 3.65/0.98  --soft_lemma_size                       3
% 3.65/0.98  --prop_impl_unit_size                   0
% 3.65/0.98  --prop_impl_unit                        []
% 3.65/0.98  --share_sel_clauses                     true
% 3.65/0.98  --reset_solvers                         false
% 3.65/0.98  --bc_imp_inh                            [conj_cone]
% 3.65/0.98  --conj_cone_tolerance                   3.
% 3.65/0.98  --extra_neg_conj                        none
% 3.65/0.98  --large_theory_mode                     true
% 3.65/0.98  --prolific_symb_bound                   200
% 3.65/0.98  --lt_threshold                          2000
% 3.65/0.98  --clause_weak_htbl                      true
% 3.65/0.98  --gc_record_bc_elim                     false
% 3.65/0.98  
% 3.65/0.98  ------ Preprocessing Options
% 3.65/0.98  
% 3.65/0.98  --preprocessing_flag                    true
% 3.65/0.98  --time_out_prep_mult                    0.1
% 3.65/0.98  --splitting_mode                        input
% 3.65/0.98  --splitting_grd                         true
% 3.65/0.98  --splitting_cvd                         false
% 3.65/0.98  --splitting_cvd_svl                     false
% 3.65/0.98  --splitting_nvd                         32
% 3.65/0.98  --sub_typing                            true
% 3.65/0.98  --prep_gs_sim                           true
% 3.65/0.98  --prep_unflatten                        true
% 3.65/0.98  --prep_res_sim                          true
% 3.65/0.98  --prep_upred                            true
% 3.65/0.98  --prep_sem_filter                       exhaustive
% 3.65/0.98  --prep_sem_filter_out                   false
% 3.65/0.98  --pred_elim                             true
% 3.65/0.98  --res_sim_input                         true
% 3.65/0.98  --eq_ax_congr_red                       true
% 3.65/0.98  --pure_diseq_elim                       true
% 3.65/0.98  --brand_transform                       false
% 3.65/0.98  --non_eq_to_eq                          false
% 3.65/0.98  --prep_def_merge                        true
% 3.65/0.98  --prep_def_merge_prop_impl              false
% 3.65/0.98  --prep_def_merge_mbd                    true
% 3.65/0.98  --prep_def_merge_tr_red                 false
% 3.65/0.98  --prep_def_merge_tr_cl                  false
% 3.65/0.98  --smt_preprocessing                     true
% 3.65/0.98  --smt_ac_axioms                         fast
% 3.65/0.98  --preprocessed_out                      false
% 3.65/0.98  --preprocessed_stats                    false
% 3.65/0.98  
% 3.65/0.98  ------ Abstraction refinement Options
% 3.65/0.98  
% 3.65/0.98  --abstr_ref                             []
% 3.65/0.98  --abstr_ref_prep                        false
% 3.65/0.98  --abstr_ref_until_sat                   false
% 3.65/0.98  --abstr_ref_sig_restrict                funpre
% 3.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.98  --abstr_ref_under                       []
% 3.65/0.98  
% 3.65/0.98  ------ SAT Options
% 3.65/0.98  
% 3.65/0.98  --sat_mode                              false
% 3.65/0.98  --sat_fm_restart_options                ""
% 3.65/0.98  --sat_gr_def                            false
% 3.65/0.98  --sat_epr_types                         true
% 3.65/0.98  --sat_non_cyclic_types                  false
% 3.65/0.98  --sat_finite_models                     false
% 3.65/0.98  --sat_fm_lemmas                         false
% 3.65/0.98  --sat_fm_prep                           false
% 3.65/0.98  --sat_fm_uc_incr                        true
% 3.65/0.98  --sat_out_model                         small
% 3.65/0.98  --sat_out_clauses                       false
% 3.65/0.98  
% 3.65/0.98  ------ QBF Options
% 3.65/0.98  
% 3.65/0.98  --qbf_mode                              false
% 3.65/0.98  --qbf_elim_univ                         false
% 3.65/0.98  --qbf_dom_inst                          none
% 3.65/0.98  --qbf_dom_pre_inst                      false
% 3.65/0.98  --qbf_sk_in                             false
% 3.65/0.98  --qbf_pred_elim                         true
% 3.65/0.98  --qbf_split                             512
% 3.65/0.98  
% 3.65/0.98  ------ BMC1 Options
% 3.65/0.98  
% 3.65/0.98  --bmc1_incremental                      false
% 3.65/0.98  --bmc1_axioms                           reachable_all
% 3.65/0.98  --bmc1_min_bound                        0
% 3.65/0.98  --bmc1_max_bound                        -1
% 3.65/0.98  --bmc1_max_bound_default                -1
% 3.65/0.98  --bmc1_symbol_reachability              true
% 3.65/0.98  --bmc1_property_lemmas                  false
% 3.65/0.98  --bmc1_k_induction                      false
% 3.65/0.98  --bmc1_non_equiv_states                 false
% 3.65/0.98  --bmc1_deadlock                         false
% 3.65/0.98  --bmc1_ucm                              false
% 3.65/0.98  --bmc1_add_unsat_core                   none
% 3.65/0.98  --bmc1_unsat_core_children              false
% 3.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.98  --bmc1_out_stat                         full
% 3.65/0.98  --bmc1_ground_init                      false
% 3.65/0.98  --bmc1_pre_inst_next_state              false
% 3.65/0.98  --bmc1_pre_inst_state                   false
% 3.65/0.98  --bmc1_pre_inst_reach_state             false
% 3.65/0.98  --bmc1_out_unsat_core                   false
% 3.65/0.98  --bmc1_aig_witness_out                  false
% 3.65/0.98  --bmc1_verbose                          false
% 3.65/0.98  --bmc1_dump_clauses_tptp                false
% 3.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.98  --bmc1_dump_file                        -
% 3.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.98  --bmc1_ucm_extend_mode                  1
% 3.65/0.98  --bmc1_ucm_init_mode                    2
% 3.65/0.98  --bmc1_ucm_cone_mode                    none
% 3.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.98  --bmc1_ucm_relax_model                  4
% 3.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.98  --bmc1_ucm_layered_model                none
% 3.65/0.98  --bmc1_ucm_max_lemma_size               10
% 3.65/0.98  
% 3.65/0.98  ------ AIG Options
% 3.65/0.98  
% 3.65/0.98  --aig_mode                              false
% 3.65/0.98  
% 3.65/0.98  ------ Instantiation Options
% 3.65/0.98  
% 3.65/0.98  --instantiation_flag                    true
% 3.65/0.98  --inst_sos_flag                         false
% 3.65/0.98  --inst_sos_phase                        true
% 3.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.98  --inst_lit_sel_side                     none
% 3.65/0.98  --inst_solver_per_active                1400
% 3.65/0.98  --inst_solver_calls_frac                1.
% 3.65/0.98  --inst_passive_queue_type               priority_queues
% 3.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.98  --inst_passive_queues_freq              [25;2]
% 3.65/0.98  --inst_dismatching                      true
% 3.65/0.98  --inst_eager_unprocessed_to_passive     true
% 3.65/0.98  --inst_prop_sim_given                   true
% 3.65/0.98  --inst_prop_sim_new                     false
% 3.65/0.98  --inst_subs_new                         false
% 3.65/0.98  --inst_eq_res_simp                      false
% 3.65/0.98  --inst_subs_given                       false
% 3.65/0.98  --inst_orphan_elimination               true
% 3.65/0.98  --inst_learning_loop_flag               true
% 3.65/0.98  --inst_learning_start                   3000
% 3.65/0.98  --inst_learning_factor                  2
% 3.65/0.98  --inst_start_prop_sim_after_learn       3
% 3.65/0.98  --inst_sel_renew                        solver
% 3.65/0.98  --inst_lit_activity_flag                true
% 3.65/0.98  --inst_restr_to_given                   false
% 3.65/0.98  --inst_activity_threshold               500
% 3.65/0.98  --inst_out_proof                        true
% 3.65/0.98  
% 3.65/0.98  ------ Resolution Options
% 3.65/0.98  
% 3.65/0.98  --resolution_flag                       false
% 3.65/0.98  --res_lit_sel                           adaptive
% 3.65/0.98  --res_lit_sel_side                      none
% 3.65/0.98  --res_ordering                          kbo
% 3.65/0.98  --res_to_prop_solver                    active
% 3.65/0.98  --res_prop_simpl_new                    false
% 3.65/0.98  --res_prop_simpl_given                  true
% 3.65/0.98  --res_passive_queue_type                priority_queues
% 3.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.98  --res_passive_queues_freq               [15;5]
% 3.65/0.98  --res_forward_subs                      full
% 3.65/0.98  --res_backward_subs                     full
% 3.65/0.98  --res_forward_subs_resolution           true
% 3.65/0.98  --res_backward_subs_resolution          true
% 3.65/0.98  --res_orphan_elimination                true
% 3.65/0.98  --res_time_limit                        2.
% 3.65/0.98  --res_out_proof                         true
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Options
% 3.65/0.98  
% 3.65/0.98  --superposition_flag                    true
% 3.65/0.98  --sup_passive_queue_type                priority_queues
% 3.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.98  --demod_completeness_check              fast
% 3.65/0.98  --demod_use_ground                      true
% 3.65/0.98  --sup_to_prop_solver                    passive
% 3.65/0.98  --sup_prop_simpl_new                    true
% 3.65/0.98  --sup_prop_simpl_given                  true
% 3.65/0.98  --sup_fun_splitting                     false
% 3.65/0.98  --sup_smt_interval                      50000
% 3.65/0.98  
% 3.65/0.98  ------ Superposition Simplification Setup
% 3.65/0.98  
% 3.65/0.98  --sup_indices_passive                   []
% 3.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_full_bw                           [BwDemod]
% 3.65/0.98  --sup_immed_triv                        [TrivRules]
% 3.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_immed_bw_main                     []
% 3.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.65/0.98  
% 3.65/0.98  ------ Combination Options
% 3.65/0.98  
% 3.65/0.98  --comb_res_mult                         3
% 3.65/0.98  --comb_sup_mult                         2
% 3.65/0.98  --comb_inst_mult                        10
% 3.65/0.98  
% 3.65/0.98  ------ Debug Options
% 3.65/0.98  
% 3.65/0.98  --dbg_backtrace                         false
% 3.65/0.98  --dbg_dump_prop_clauses                 false
% 3.65/0.98  --dbg_dump_prop_clauses_file            -
% 3.65/0.98  --dbg_out_stat                          false
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  ------ Proving...
% 3.65/0.98  
% 3.65/0.98  
% 3.65/0.98  % SZS status Theorem for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98   Resolution empty clause
% 3.65/0.98  
% 3.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.98  
% 3.65/0.98  fof(f15,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f35,plain,(
% 3.65/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f15])).
% 3.65/0.98  
% 3.65/0.98  fof(f75,plain,(
% 3.65/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f35])).
% 3.65/0.98  
% 3.65/0.98  fof(f12,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f32,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f12])).
% 3.65/0.98  
% 3.65/0.98  fof(f70,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f32])).
% 3.65/0.98  
% 3.65/0.98  fof(f10,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f30,plain,(
% 3.65/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f10])).
% 3.65/0.98  
% 3.65/0.98  fof(f67,plain,(
% 3.65/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f30])).
% 3.65/0.98  
% 3.65/0.98  fof(f7,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f27,plain,(
% 3.65/0.98    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.65/0.98    inference(ennf_transformation,[],[f7])).
% 3.65/0.98  
% 3.65/0.98  fof(f64,plain,(
% 3.65/0.98    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f19,conjecture,(
% 3.65/0.98    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f20,negated_conjecture,(
% 3.65/0.98    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 3.65/0.98    inference(negated_conjecture,[],[f19])).
% 3.65/0.98  
% 3.65/0.98  fof(f21,plain,(
% 3.65/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 3.65/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.65/0.98  
% 3.65/0.98  fof(f40,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & (m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0))) & l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f21])).
% 3.65/0.98  
% 3.65/0.98  fof(f41,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f40])).
% 3.65/0.98  
% 3.65/0.98  fof(f52,plain,(
% 3.65/0.98    ( ! [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_pre_topc(sK2,X0) & ~v1_tex_2(sK2,X0))) )),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f51,plain,(
% 3.65/0.98    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,sK1) & ~v1_tex_2(X1,sK1)) & l1_pre_topc(sK1))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f53,plain,(
% 3.65/0.98    (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK1) & ~v1_tex_2(sK2,sK1)) & l1_pre_topc(sK1)),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f52,f51])).
% 3.65/0.98  
% 3.65/0.98  fof(f83,plain,(
% 3.65/0.98    l1_pre_topc(sK1)),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f4,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f22,plain,(
% 3.65/0.98    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f4])).
% 3.65/0.98  
% 3.65/0.98  fof(f23,plain,(
% 3.65/0.98    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f22])).
% 3.65/0.98  
% 3.65/0.98  fof(f59,plain,(
% 3.65/0.98    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f23])).
% 3.65/0.98  
% 3.65/0.98  fof(f63,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f27])).
% 3.65/0.98  
% 3.65/0.98  fof(f11,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f31,plain,(
% 3.65/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.65/0.98    inference(ennf_transformation,[],[f11])).
% 3.65/0.98  
% 3.65/0.98  fof(f68,plain,(
% 3.65/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f31])).
% 3.65/0.98  
% 3.65/0.98  fof(f8,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f28,plain,(
% 3.65/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f8])).
% 3.65/0.98  
% 3.65/0.98  fof(f65,plain,(
% 3.65/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f28])).
% 3.65/0.98  
% 3.65/0.98  fof(f6,axiom,(
% 3.65/0.98    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f26,plain,(
% 3.65/0.98    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f6])).
% 3.65/0.98  
% 3.65/0.98  fof(f62,plain,(
% 3.65/0.98    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f26])).
% 3.65/0.98  
% 3.65/0.98  fof(f5,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f24,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f5])).
% 3.65/0.98  
% 3.65/0.98  fof(f25,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f24])).
% 3.65/0.98  
% 3.65/0.98  fof(f44,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f25])).
% 3.65/0.98  
% 3.65/0.98  fof(f61,plain,(
% 3.65/0.98    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f44])).
% 3.65/0.98  
% 3.65/0.98  fof(f89,plain,(
% 3.65/0.98    ( ! [X2,X0] : (k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(equality_resolution,[],[f61])).
% 3.65/0.98  
% 3.65/0.98  fof(f14,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f34,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f14])).
% 3.65/0.98  
% 3.65/0.98  fof(f73,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f34])).
% 3.65/0.98  
% 3.65/0.98  fof(f74,plain,(
% 3.65/0.98    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f34])).
% 3.65/0.98  
% 3.65/0.98  fof(f3,axiom,(
% 3.65/0.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f58,plain,(
% 3.65/0.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f3])).
% 3.65/0.98  
% 3.65/0.98  fof(f2,axiom,(
% 3.65/0.98    ! [X0] : k2_subset_1(X0) = X0),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f57,plain,(
% 3.65/0.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.65/0.98    inference(cnf_transformation,[],[f2])).
% 3.65/0.98  
% 3.65/0.98  fof(f85,plain,(
% 3.65/0.98    m1_pre_topc(sK2,sK1)),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f17,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f37,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f17])).
% 3.65/0.98  
% 3.65/0.98  fof(f38,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(flattening,[],[f37])).
% 3.65/0.98  
% 3.65/0.98  fof(f46,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(nnf_transformation,[],[f38])).
% 3.65/0.98  
% 3.65/0.98  fof(f47,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(rectify,[],[f46])).
% 3.65/0.98  
% 3.65/0.98  fof(f48,plain,(
% 3.65/0.98    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.65/0.98    introduced(choice_axiom,[])).
% 3.65/0.98  
% 3.65/0.98  fof(f49,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 3.65/0.98  
% 3.65/0.98  fof(f79,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f49])).
% 3.65/0.98  
% 3.65/0.98  fof(f84,plain,(
% 3.65/0.98    ~v1_tex_2(sK2,sK1)),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  fof(f78,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f49])).
% 3.65/0.98  
% 3.65/0.98  fof(f18,axiom,(
% 3.65/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f39,plain,(
% 3.65/0.98    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.98    inference(ennf_transformation,[],[f18])).
% 3.65/0.98  
% 3.65/0.98  fof(f50,plain,(
% 3.65/0.98    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.65/0.98    inference(nnf_transformation,[],[f39])).
% 3.65/0.98  
% 3.65/0.98  fof(f82,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.65/0.98    inference(cnf_transformation,[],[f50])).
% 3.65/0.98  
% 3.65/0.98  fof(f80,plain,(
% 3.65/0.98    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f49])).
% 3.65/0.98  
% 3.65/0.98  fof(f9,axiom,(
% 3.65/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/0.98  
% 3.65/0.98  fof(f29,plain,(
% 3.65/0.98    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.65/0.98    inference(ennf_transformation,[],[f9])).
% 3.65/0.98  
% 3.65/0.98  fof(f66,plain,(
% 3.65/0.98    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.65/0.98    inference(cnf_transformation,[],[f29])).
% 3.65/0.98  
% 3.65/0.98  fof(f86,plain,(
% 3.65/0.98    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.65/0.98    inference(cnf_transformation,[],[f53])).
% 3.65/0.98  
% 3.65/0.98  cnf(c_21,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3105,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_16,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3108,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 3.65/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5351,plain,
% 3.65/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3105,c_3108]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13,plain,
% 3.65/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 3.65/0.98      | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3111,plain,
% 3.65/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.65/0.98      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3114,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3712,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3111,c_3114]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12109,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top ),
% 3.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5351,c_3712]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12110,plain,
% 3.65/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X0) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_12109]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_32,negated_conjecture,
% 3.65/0.98      ( l1_pre_topc(sK1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3095,plain,
% 3.65/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5,plain,
% 3.65/0.98      ( ~ l1_pre_topc(X0)
% 3.65/0.98      | ~ v1_pre_topc(X0)
% 3.65/0.98      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3117,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4469,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3712,c_3117]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3360,plain,
% 3.65/0.98      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.65/0.98      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.65/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3361,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.65/0.98      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3360]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_10,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 3.65/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3113,plain,
% 3.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3568,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3111,c_3113]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8623,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_4469,c_3361,c_3568,c_3712]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8624,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_8623]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8631,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3095,c_8624]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_15,plain,
% 3.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.65/0.98      | X2 = X1
% 3.65/0.98      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3109,plain,
% 3.65/0.98      ( X0 = X1
% 3.65/0.98      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 3.65/0.98      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9007,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 3.65/0.98      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 3.65/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_8631,c_3109]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9405,plain,
% 3.65/0.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 3.65/0.98      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 3.65/0.98      inference(equality_resolution,[status(thm)],[c_9007]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_33,plain,
% 3.65/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_75,plain,
% 3.65/0.98      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_77,plain,
% 3.65/0.98      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top
% 3.65/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_75]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9844,plain,
% 3.65/0.98      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_9405,c_33,c_77]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_11,plain,
% 3.65/0.98      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_8,plain,
% 3.65/0.98      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_351,plain,
% 3.65/0.98      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 3.65/0.98      inference(resolution,[status(thm)],[c_11,c_8]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3093,plain,
% 3.65/0.98      ( k2_struct_0(X0) = u1_struct_0(X0) | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_351]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4180,plain,
% 3.65/0.98      ( k2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3712,c_3093]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_4649,plain,
% 3.65/0.98      ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_3095,c_4180]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | ~ v1_pre_topc(X0)
% 3.65/0.98      | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
% 3.65/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_3116,plain,
% 3.65/0.98      ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
% 3.65/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.65/0.98      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5925,plain,
% 3.65/0.98      ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_4649,c_3116]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_5967,plain,
% 3.65/0.98      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 3.65/0.98      inference(light_normalisation,[status(thm)],[c_5925,c_4649]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_57,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_59,plain,
% 3.65/0.98      ( m1_pre_topc(sK1,sK1) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_57]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_20,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | ~ l1_pre_topc(X1)
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 3.65/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_60,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_62,plain,
% 3.65/0.98      ( m1_pre_topc(sK1,sK1) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.65/0.98      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_60]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6328,plain,
% 3.65/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.65/0.98      | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.65/0.98      inference(global_propositional_subsumption,
% 3.65/0.98                [status(thm)],
% 3.65/0.98                [c_5967,c_33,c_59,c_62]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_6329,plain,
% 3.65/0.98      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(renaming,[status(thm)],[c_6328]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9851,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.98      inference(demodulation,[status(thm)],[c_9844,c_6329]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_12128,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 3.65/0.98      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.98      inference(superposition,[status(thm)],[c_12110,c_9851]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_19,plain,
% 3.65/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 3.65/0.98      | ~ l1_pre_topc(X1) ),
% 3.65/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_63,plain,
% 3.65/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.65/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_65,plain,
% 3.65/0.98      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
% 3.65/0.98      | m1_pre_topc(sK1,sK1) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_63]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_9887,plain,
% 3.65/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 3.65/0.98      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 3.65/0.98      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.65/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.98      inference(instantiation,[status(thm)],[c_9851]) ).
% 3.65/0.98  
% 3.65/0.98  cnf(c_13450,plain,
% 3.65/0.98      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.65/0.98      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_12128,c_33,c_59,c_65,c_9887]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13451,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_13450]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4,plain,
% 3.65/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3118,plain,
% 3.65/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3,plain,
% 3.65/0.99      ( k2_subset_1(X0) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3131,plain,
% 3.65/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_3118,c_3]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13456,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 3.65/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_13451,c_3131]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13468,plain,
% 3.65/0.99      ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK1))) = u1_struct_0(sK1) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_13456,c_9844]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3452,plain,
% 3.65/0.99      ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3095,c_3093]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5924,plain,
% 3.65/0.99      ( k1_pre_topc(X0,k2_struct_0(sK1)) = sK1
% 3.65/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | v1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3452,c_3116]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5978,plain,
% 3.65/0.99      ( k1_pre_topc(X0,u1_struct_0(sK1)) = sK1
% 3.65/0.99      | m1_pre_topc(sK1,X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | v1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_5924,c_3452]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14040,plain,
% 3.65/0.99      ( k1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1)),u1_struct_0(sK1)) = sK1
% 3.65/0.99      | m1_pre_topc(sK1,k1_pre_topc(sK1,u1_struct_0(sK1))) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.65/0.99      | l1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1))) != iProver_top
% 3.65/0.99      | v1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_13468,c_5978]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_30,negated_conjecture,
% 3.65/0.99      ( m1_pre_topc(sK2,sK1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_35,plain,
% 3.65/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3097,plain,
% 3.65/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_24,plain,
% 3.65/0.99      ( v1_tex_2(X0,X1)
% 3.65/0.99      | ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | sK0(X1,X0) = u1_struct_0(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3102,plain,
% 3.65/0.99      ( sK0(X0,X1) = u1_struct_0(X1)
% 3.65/0.99      | v1_tex_2(X1,X0) = iProver_top
% 3.65/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5810,plain,
% 3.65/0.99      ( sK0(sK1,sK2) = u1_struct_0(sK2)
% 3.65/0.99      | v1_tex_2(sK2,sK1) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3097,c_3102]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_31,negated_conjecture,
% 3.65/0.99      ( ~ v1_tex_2(sK2,sK1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_707,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | ~ l1_pre_topc(X1)
% 3.65/0.99      | sK0(X1,X0) = u1_struct_0(X0)
% 3.65/0.99      | sK2 != X0
% 3.65/0.99      | sK1 != X1 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_708,plain,
% 3.65/0.99      ( ~ m1_pre_topc(sK2,sK1)
% 3.65/0.99      | ~ l1_pre_topc(sK1)
% 3.65/0.99      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_707]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6118,plain,
% 3.65/0.99      ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_5810,c_32,c_30,c_708]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_25,plain,
% 3.65/0.99      ( v1_tex_2(X0,X1)
% 3.65/0.99      | ~ m1_pre_topc(X0,X1)
% 3.65/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.65/0.99      | ~ l1_pre_topc(X1) ),
% 3.65/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3101,plain,
% 3.65/0.99      ( v1_tex_2(X0,X1) = iProver_top
% 3.65/0.99      | m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6122,plain,
% 3.65/0.99      ( v1_tex_2(sK2,sK1) = iProver_top
% 3.65/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6118,c_3101]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_34,plain,
% 3.65/0.99      ( v1_tex_2(sK2,sK1) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6341,plain,
% 3.65/0.99      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6122,c_33,c_34,c_35]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_27,plain,
% 3.65/0.99      ( v1_subset_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | X0 = X1 ),
% 3.65/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3099,plain,
% 3.65/0.99      ( X0 = X1
% 3.65/0.99      | v1_subset_1(X0,X1) = iProver_top
% 3.65/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6347,plain,
% 3.65/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.65/0.99      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6341,c_3099]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_23,plain,
% 3.65/0.99      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 3.65/0.99      | v1_tex_2(X1,X0)
% 3.65/0.99      | ~ m1_pre_topc(X1,X0)
% 3.65/0.99      | ~ l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3103,plain,
% 3.65/0.99      ( v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) != iProver_top
% 3.65/0.99      | v1_tex_2(X1,X0) = iProver_top
% 3.65/0.99      | m1_pre_topc(X1,X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6121,plain,
% 3.65/0.99      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.65/0.99      | v1_tex_2(sK2,sK1) = iProver_top
% 3.65/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6118,c_3103]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6753,plain,
% 3.65/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_6347,c_33,c_34,c_35,c_6121]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3107,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6828,plain,
% 3.65/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) = iProver_top
% 3.65/0.99      | m1_pre_topc(sK2,X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_6753,c_3107]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6955,plain,
% 3.65/0.99      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) = iProver_top
% 3.65/0.99      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_6828]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12,plain,
% 3.65/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.65/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3112,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5326,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3107,c_3112]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5485,plain,
% 3.65/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3097,c_5326]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5559,plain,
% 3.65/0.99      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5485,c_33]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5565,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_5559,c_3117]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3106,plain,
% 3.65/0.99      ( m1_pre_topc(X0,X1) != iProver_top
% 3.65/0.99      | l1_pre_topc(X1) != iProver_top
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5023,plain,
% 3.65/0.99      ( l1_pre_topc(sK1) != iProver_top
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3097,c_3106]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5436,plain,
% 3.65/0.99      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.65/0.99      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 3.65/0.99      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_3360]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5437,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.65/0.99      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_5436]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5645,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_5565,c_33,c_5023,c_5437,c_5485]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5654,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(X0,X1)
% 3.65/0.99      | u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = X0
% 3.65/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_5645,c_3109]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5699,plain,
% 3.65/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2)
% 3.65/0.99      | m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) != iProver_top ),
% 3.65/0.99      inference(equality_resolution,[status(thm)],[c_5654]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3692,plain,
% 3.65/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
% 3.65/0.99      | ~ l1_pre_topc(sK2) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3697,plain,
% 3.65/0.99      ( m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3692]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4147,plain,
% 3.65/0.99      ( ~ m1_pre_topc(sK2,X0) | ~ l1_pre_topc(X0) | l1_pre_topc(sK2) ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4148,plain,
% 3.65/0.99      ( m1_pre_topc(sK2,X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_4147]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4150,plain,
% 3.65/0.99      ( m1_pre_topc(sK2,sK1) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK2) = iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_4148]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12353,plain,
% 3.65/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(sK2) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_5699,c_33,c_35,c_3697,c_4150]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12355,plain,
% 3.65/0.99      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_12353,c_6753]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4189,plain,
% 3.65/0.99      ( l1_pre_topc(sK2) = iProver_top | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3097,c_3112]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4235,plain,
% 3.65/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_4189,c_33,c_35,c_4150]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_4651,plain,
% 3.65/0.99      ( k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4235,c_4180]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5928,plain,
% 3.65/0.99      ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_4651,c_3116]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_5934,plain,
% 3.65/0.99      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_5928,c_4651]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_11821,plain,
% 3.65/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_5934,c_33,c_5023]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_11822,plain,
% 3.65/0.99      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(renaming,[status(thm)],[c_11821]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_11827,plain,
% 3.65/0.99      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_11822,c_6753]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12357,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.65/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_12355,c_11827]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_12373,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 3.65/0.99      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) != iProver_top
% 3.65/0.99      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.65/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.65/0.99      inference(instantiation,[status(thm)],[c_12357]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_29,negated_conjecture,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_6768,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_6753,c_29]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13470,plain,
% 3.65/0.99      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_13456,c_6768]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14193,plain,
% 3.65/0.99      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.65/0.99      inference(global_propositional_subsumption,
% 3.65/0.99                [status(thm)],
% 3.65/0.99                [c_14040,c_33,c_35,c_6955,c_12373,c_13470]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14198,plain,
% 3.65/0.99      ( $false ),
% 3.65/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_14193,c_3131]) ).
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  ------                               Statistics
% 3.65/0.99  
% 3.65/0.99  ------ General
% 3.65/0.99  
% 3.65/0.99  abstr_ref_over_cycles:                  0
% 3.65/0.99  abstr_ref_under_cycles:                 0
% 3.65/0.99  gc_basic_clause_elim:                   0
% 3.65/0.99  forced_gc_time:                         0
% 3.65/0.99  parsing_time:                           0.009
% 3.65/0.99  unif_index_cands_time:                  0.
% 3.65/0.99  unif_index_add_time:                    0.
% 3.65/0.99  orderings_time:                         0.
% 3.65/0.99  out_proof_time:                         0.014
% 3.65/0.99  total_time:                             0.374
% 3.65/0.99  num_of_symbols:                         49
% 3.65/0.99  num_of_terms:                           13958
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing
% 3.65/0.99  
% 3.65/0.99  num_of_splits:                          0
% 3.65/0.99  num_of_split_atoms:                     0
% 3.65/0.99  num_of_reused_defs:                     0
% 3.65/0.99  num_eq_ax_congr_red:                    13
% 3.65/0.99  num_of_sem_filtered_clauses:            1
% 3.65/0.99  num_of_subtypes:                        0
% 3.65/0.99  monotx_restored_types:                  0
% 3.65/0.99  sat_num_of_epr_types:                   0
% 3.65/0.99  sat_num_of_non_cyclic_types:            0
% 3.65/0.99  sat_guarded_non_collapsed_types:        0
% 3.65/0.99  num_pure_diseq_elim:                    0
% 3.65/0.99  simp_replaced_by:                       0
% 3.65/0.99  res_preprocessed:                       152
% 3.65/0.99  prep_upred:                             0
% 3.65/0.99  prep_unflattend:                        76
% 3.65/0.99  smt_new_axioms:                         0
% 3.65/0.99  pred_elim_cands:                        7
% 3.65/0.99  pred_elim:                              1
% 3.65/0.99  pred_elim_cl:                           1
% 3.65/0.99  pred_elim_cycles:                       9
% 3.65/0.99  merged_defs:                            0
% 3.65/0.99  merged_defs_ncl:                        0
% 3.65/0.99  bin_hyper_res:                          0
% 3.65/0.99  prep_cycles:                            4
% 3.65/0.99  pred_elim_time:                         0.035
% 3.65/0.99  splitting_time:                         0.
% 3.65/0.99  sem_filter_time:                        0.
% 3.65/0.99  monotx_time:                            0.
% 3.65/0.99  subtype_inf_time:                       0.
% 3.65/0.99  
% 3.65/0.99  ------ Problem properties
% 3.65/0.99  
% 3.65/0.99  clauses:                                30
% 3.65/0.99  conjectures:                            4
% 3.65/0.99  epr:                                    7
% 3.65/0.99  horn:                                   27
% 3.65/0.99  ground:                                 4
% 3.65/0.99  unary:                                  7
% 3.65/0.99  binary:                                 6
% 3.65/0.99  lits:                                   79
% 3.65/0.99  lits_eq:                                13
% 3.65/0.99  fd_pure:                                0
% 3.65/0.99  fd_pseudo:                              0
% 3.65/0.99  fd_cond:                                0
% 3.65/0.99  fd_pseudo_cond:                         4
% 3.65/0.99  ac_symbols:                             0
% 3.65/0.99  
% 3.65/0.99  ------ Propositional Solver
% 3.65/0.99  
% 3.65/0.99  prop_solver_calls:                      28
% 3.65/0.99  prop_fast_solver_calls:                 1682
% 3.65/0.99  smt_solver_calls:                       0
% 3.65/0.99  smt_fast_solver_calls:                  0
% 3.65/0.99  prop_num_of_clauses:                    4136
% 3.65/0.99  prop_preprocess_simplified:             10455
% 3.65/0.99  prop_fo_subsumed:                       73
% 3.65/0.99  prop_solver_time:                       0.
% 3.65/0.99  smt_solver_time:                        0.
% 3.65/0.99  smt_fast_solver_time:                   0.
% 3.65/0.99  prop_fast_solver_time:                  0.
% 3.65/0.99  prop_unsat_core_time:                   0.
% 3.65/0.99  
% 3.65/0.99  ------ QBF
% 3.65/0.99  
% 3.65/0.99  qbf_q_res:                              0
% 3.65/0.99  qbf_num_tautologies:                    0
% 3.65/0.99  qbf_prep_cycles:                        0
% 3.65/0.99  
% 3.65/0.99  ------ BMC1
% 3.65/0.99  
% 3.65/0.99  bmc1_current_bound:                     -1
% 3.65/0.99  bmc1_last_solved_bound:                 -1
% 3.65/0.99  bmc1_unsat_core_size:                   -1
% 3.65/0.99  bmc1_unsat_core_parents_size:           -1
% 3.65/0.99  bmc1_merge_next_fun:                    0
% 3.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation
% 3.65/0.99  
% 3.65/0.99  inst_num_of_clauses:                    1186
% 3.65/0.99  inst_num_in_passive:                    153
% 3.65/0.99  inst_num_in_active:                     606
% 3.65/0.99  inst_num_in_unprocessed:                427
% 3.65/0.99  inst_num_of_loops:                      620
% 3.65/0.99  inst_num_of_learning_restarts:          0
% 3.65/0.99  inst_num_moves_active_passive:          12
% 3.65/0.99  inst_lit_activity:                      0
% 3.65/0.99  inst_lit_activity_moves:                0
% 3.65/0.99  inst_num_tautologies:                   0
% 3.65/0.99  inst_num_prop_implied:                  0
% 3.65/0.99  inst_num_existing_simplified:           0
% 3.65/0.99  inst_num_eq_res_simplified:             0
% 3.65/0.99  inst_num_child_elim:                    0
% 3.65/0.99  inst_num_of_dismatching_blockings:      1531
% 3.65/0.99  inst_num_of_non_proper_insts:           1966
% 3.65/0.99  inst_num_of_duplicates:                 0
% 3.65/0.99  inst_inst_num_from_inst_to_res:         0
% 3.65/0.99  inst_dismatching_checking_time:         0.
% 3.65/0.99  
% 3.65/0.99  ------ Resolution
% 3.65/0.99  
% 3.65/0.99  res_num_of_clauses:                     0
% 3.65/0.99  res_num_in_passive:                     0
% 3.65/0.99  res_num_in_active:                      0
% 3.65/0.99  res_num_of_loops:                       156
% 3.65/0.99  res_forward_subset_subsumed:            230
% 3.65/0.99  res_backward_subset_subsumed:           0
% 3.65/0.99  res_forward_subsumed:                   0
% 3.65/0.99  res_backward_subsumed:                  0
% 3.65/0.99  res_forward_subsumption_resolution:     0
% 3.65/0.99  res_backward_subsumption_resolution:    0
% 3.65/0.99  res_clause_to_clause_subsumption:       1027
% 3.65/0.99  res_orphan_elimination:                 0
% 3.65/0.99  res_tautology_del:                      93
% 3.65/0.99  res_num_eq_res_simplified:              0
% 3.65/0.99  res_num_sel_changes:                    0
% 3.65/0.99  res_moves_from_active_to_pass:          0
% 3.65/0.99  
% 3.65/0.99  ------ Superposition
% 3.65/0.99  
% 3.65/0.99  sup_time_total:                         0.
% 3.65/0.99  sup_time_generating:                    0.
% 3.65/0.99  sup_time_sim_full:                      0.
% 3.65/0.99  sup_time_sim_immed:                     0.
% 3.65/0.99  
% 3.65/0.99  sup_num_of_clauses:                     202
% 3.65/0.99  sup_num_in_active:                      80
% 3.65/0.99  sup_num_in_passive:                     122
% 3.65/0.99  sup_num_of_loops:                       123
% 3.65/0.99  sup_fw_superposition:                   127
% 3.65/0.99  sup_bw_superposition:                   230
% 3.65/0.99  sup_immediate_simplified:               139
% 3.65/0.99  sup_given_eliminated:                   0
% 3.65/0.99  comparisons_done:                       0
% 3.65/0.99  comparisons_avoided:                    0
% 3.65/0.99  
% 3.65/0.99  ------ Simplifications
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  sim_fw_subset_subsumed:                 30
% 3.65/0.99  sim_bw_subset_subsumed:                 9
% 3.65/0.99  sim_fw_subsumed:                        42
% 3.65/0.99  sim_bw_subsumed:                        1
% 3.65/0.99  sim_fw_subsumption_res:                 7
% 3.65/0.99  sim_bw_subsumption_res:                 0
% 3.65/0.99  sim_tautology_del:                      28
% 3.65/0.99  sim_eq_tautology_del:                   28
% 3.65/0.99  sim_eq_res_simp:                        0
% 3.65/0.99  sim_fw_demodulated:                     10
% 3.65/0.99  sim_bw_demodulated:                     42
% 3.65/0.99  sim_light_normalised:                   93
% 3.65/0.99  sim_joinable_taut:                      0
% 3.65/0.99  sim_joinable_simp:                      0
% 3.65/0.99  sim_ac_normalised:                      0
% 3.65/0.99  sim_smt_subsumption:                    0
% 3.65/0.99  
%------------------------------------------------------------------------------
