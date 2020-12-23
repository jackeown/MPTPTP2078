%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:23 EST 2020

% Result     : Theorem 23.42s
% Output     : CNFRefutation 23.42s
% Verified   : 
% Statistics : Number of formulae       :  259 (2464 expanded)
%              Number of clauses        :  182 ( 754 expanded)
%              Number of leaves         :   25 ( 657 expanded)
%              Depth                    :   29
%              Number of atoms          :  784 (11962 expanded)
%              Number of equality atoms :  371 (2866 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   3 average)
%              Maximal term depth       :    5 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tex_2(X2,X0)
              & v1_tex_2(X1,X0)
              & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f45,f44,f43])).

fof(f72,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f73,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f69])).

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

fof(f74,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( v1_subset_1(X3,u1_struct_0(X0))
      | u1_struct_0(X1) != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f75,plain,(
    v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2455,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2465,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2476,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2470,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3760,plain,
    ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2476,c_2470])).

cnf(c_4105,plain,
    ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2465,c_3760])).

cnf(c_7953,plain,
    ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))) = u1_struct_0(sK2)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2455,c_4105])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_30,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_8359,plain,
    ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7953,c_30])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2456,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7952,plain,
    ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))) = u1_struct_0(sK3)
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_4105])).

cnf(c_8156,plain,
    ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7952,c_30])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2464,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | u1_struct_0(X0) != u1_struct_0(X1)
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,X2) != iProver_top
    | l1_pre_topc(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8172,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8156,c_2464])).

cnf(c_8226,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8172,c_8156])).

cnf(c_2454,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2478,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2473,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5081,plain,
    ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
    | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2476,c_2473])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2471,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9995,plain,
    ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5081,c_2471])).

cnf(c_10296,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2478,c_9995])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2474,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11574,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10296,c_2474])).

cnf(c_2768,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2846,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2768])).

cnf(c_2848,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_2847,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2852,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2847])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3148,plain,
    ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3149,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3148])).

cnf(c_4080,plain,
    ( ~ l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))
    | ~ v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))
    | g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4081,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top
    | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4080])).

cnf(c_3952,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(resolution,[status(thm)],[c_8,c_10])).

cnf(c_4652,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(k1_pre_topc(X1,X0)) ),
    inference(resolution,[status(thm)],[c_3952,c_5])).

cnf(c_4664,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) ),
    inference(resolution,[status(thm)],[c_4652,c_2])).

cnf(c_4665,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4664])).

cnf(c_70719,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11574,c_2848,c_2852,c_3149,c_4081,c_4665])).

cnf(c_70720,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_70719])).

cnf(c_70727,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK1))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1)))) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(superposition,[status(thm)],[c_2454,c_70720])).

cnf(c_19,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2462,plain,
    ( sK0(X0,X1) = u1_struct_0(X1)
    | v1_tex_2(X1,X0) = iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4582,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3)
    | v1_tex_2(sK3,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_2462])).

cnf(c_24,negated_conjecture,
    ( ~ v1_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_613,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_614,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_5856,plain,
    ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4582,c_29,c_27,c_614])).

cnf(c_20,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2461,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5859,plain,
    ( v1_tex_2(sK3,sK1) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5856,c_2461])).

cnf(c_32,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_34,plain,
    ( v1_tex_2(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_24696,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5859,c_30,c_32,c_34])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2475,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_24701,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24696,c_2475])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2479,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_24956,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK3)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24701,c_2479])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ v1_subset_1(X0,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_36,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ v1_subset_1(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | v1_subset_1(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_39,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | v1_subset_1(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_93,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1777,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1788,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_18,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2463,plain,
    ( v1_tex_2(X0,X1) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | v1_subset_1(sK0(X1,X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5866,plain,
    ( v1_tex_2(sK3,sK1) = iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5856,c_2463])).

cnf(c_5893,plain,
    ( v1_tex_2(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5866])).

cnf(c_10813,plain,
    ( ~ m1_pre_topc(sK3,X0)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_10815,plain,
    ( ~ m1_pre_topc(sK3,sK1)
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10813])).

cnf(c_1772,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3222,plain,
    ( X0 != X1
    | u1_struct_0(X2) != X1
    | u1_struct_0(X2) = X0 ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_4209,plain,
    ( X0 != u1_struct_0(X1)
    | u1_struct_0(X2) = X0
    | u1_struct_0(X2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_3222])).

cnf(c_7880,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(X2) ),
    inference(instantiation,[status(thm)],[c_4209])).

cnf(c_17335,plain,
    ( u1_struct_0(X0) != u1_struct_0(X1)
    | u1_struct_0(X0) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_7880])).

cnf(c_17339,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(sK3)
    | u1_struct_0(sK3) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_17335])).

cnf(c_216,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_217,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_216])).

cnf(c_265,plain,
    ( v1_subset_1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X0 = X1 ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_217])).

cnf(c_3208,plain,
    ( v1_subset_1(u1_struct_0(X0),X1)
    | ~ r1_tarski(u1_struct_0(X0),X1)
    | u1_struct_0(X0) = X1 ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_4186,plain,
    ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_3208])).

cnf(c_21071,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(X0))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
    | u1_struct_0(sK3) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4186])).

cnf(c_21075,plain,
    ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1))
    | u1_struct_0(sK3) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_21071])).

cnf(c_26735,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24956,c_29,c_27,c_24,c_36,c_39,c_86,c_93,c_1788,c_5893,c_10815,c_17339,c_21075])).

cnf(c_70874,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = k1_pre_topc(sK1,u1_struct_0(sK3)) ),
    inference(light_normalisation,[status(thm)],[c_70727,c_8156,c_26735])).

cnf(c_78777,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8226,c_70874])).

cnf(c_78789,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8359,c_78777])).

cnf(c_78903,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78789,c_8359])).

cnf(c_27000,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_26735,c_2465])).

cnf(c_29604,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_27000,c_30])).

cnf(c_29605,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_29604])).

cnf(c_26984,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_26735,c_2473])).

cnf(c_34457,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_26984,c_30])).

cnf(c_34458,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(renaming,[status(thm)],[c_34457])).

cnf(c_34465,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2476,c_34458])).

cnf(c_8375,plain,
    ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8359,c_2464])).

cnf(c_8429,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(X0) != u1_struct_0(sK2)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8375,c_8359])).

cnf(c_78988,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_8429])).

cnf(c_26,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_78993,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_78988,c_26])).

cnf(c_79296,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_34465,c_78993])).

cnf(c_31,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_79680,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79296,c_30,c_31])).

cnf(c_79681,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_79680])).

cnf(c_79687,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | m1_pre_topc(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_29605,c_79681])).

cnf(c_79701,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_79687,c_31])).

cnf(c_86585,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | u1_struct_0(sK3) != u1_struct_0(sK2)
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_78903,c_79701])).

cnf(c_24702,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_24696,c_2473])).

cnf(c_78799,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
    | m1_pre_topc(sK3,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_78777])).

cnf(c_78935,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
    | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK1) != iProver_top
    | m1_pre_topc(sK3,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_78799])).

cnf(c_86594,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_86585,c_30,c_32,c_24702,c_78935])).

cnf(c_15,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2466,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2469,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4880,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2469])).

cnf(c_2748,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

cnf(c_2749,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2748])).

cnf(c_5305,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_30,c_2749])).

cnf(c_5306,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_5305])).

cnf(c_5314,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2466,c_5306])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2468,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4812,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_2468])).

cnf(c_5129,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4812,c_2471])).

cnf(c_5166,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5129])).

cnf(c_5337,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5314,c_30,c_31,c_5166])).

cnf(c_86683,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_86594,c_5337])).

cnf(c_8168,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8156,c_2465])).

cnf(c_92099,plain,
    ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_86683,c_8168])).

cnf(c_1773,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2859,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(X3))
    | X2 != X0
    | u1_struct_0(X3) != X1 ),
    inference(instantiation,[status(thm)],[c_1773])).

cnf(c_3218,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(X2,u1_struct_0(X3))
    | X2 != X0
    | u1_struct_0(X3) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2859])).

cnf(c_4542,plain,
    ( r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
    | X0 != u1_struct_0(X2)
    | u1_struct_0(X1) != u1_struct_0(X3) ),
    inference(instantiation,[status(thm)],[c_3218])).

cnf(c_9130,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
    | u1_struct_0(X3) != u1_struct_0(X1)
    | u1_struct_0(X2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4542])).

cnf(c_18891,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
    | u1_struct_0(X2) != u1_struct_0(X0)
    | u1_struct_0(sK2) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_9130])).

cnf(c_32586,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
    | u1_struct_0(X1) != u1_struct_0(X0)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_18891])).

cnf(c_78386,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
    | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
    | u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_32586])).

cnf(c_78394,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK3)
    | u1_struct_0(sK2) != u1_struct_0(sK2)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_78386])).

cnf(c_78396,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK1) != u1_struct_0(sK3)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
    | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_78394])).

cnf(c_4,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_23839,plain,
    ( ~ v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1774,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5072,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | X0 != u1_struct_0(sK2)
    | X1 != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1774])).

cnf(c_5506,plain,
    ( v1_subset_1(X0,u1_struct_0(X1))
    | ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | X0 != u1_struct_0(sK2)
    | u1_struct_0(X1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_5072])).

cnf(c_13821,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(X0))
    | u1_struct_0(X0) != u1_struct_0(sK1)
    | k2_subset_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_5506])).

cnf(c_23838,plain,
    ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(sK2))
    | u1_struct_0(sK2) != u1_struct_0(sK1)
    | k2_subset_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_13821])).

cnf(c_4689,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),X0)
    | X0 = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8123,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_4689])).

cnf(c_22420,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_8123])).

cnf(c_22423,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22420])).

cnf(c_1771,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_10506,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1771])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4699,plain,
    ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_7123,plain,
    ( k2_subset_1(u1_struct_0(sK2)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_4699])).

cnf(c_3590,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_3591,plain,
    ( m1_pre_topc(sK2,sK1) != iProver_top
    | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3590])).

cnf(c_2856,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2768])).

cnf(c_3457,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2856])).

cnf(c_21,plain,
    ( ~ v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_632,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_633,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_635,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_633,c_29,c_28])).

cnf(c_636,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_635])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92099,c_78396,c_23839,c_23838,c_22423,c_21075,c_17339,c_10815,c_10506,c_7123,c_5893,c_3591,c_3590,c_3457,c_2749,c_1788,c_636,c_93,c_86,c_39,c_36,c_24,c_27,c_31,c_28,c_30,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:29:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 23.42/3.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.42/3.49  
% 23.42/3.49  ------  iProver source info
% 23.42/3.49  
% 23.42/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.42/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.42/3.49  git: non_committed_changes: false
% 23.42/3.49  git: last_make_outside_of_git: false
% 23.42/3.49  
% 23.42/3.49  ------ 
% 23.42/3.49  ------ Parsing...
% 23.42/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.42/3.49  
% 23.42/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.42/3.49  ------ Proving...
% 23.42/3.49  ------ Problem Properties 
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  clauses                                 29
% 23.42/3.49  conjectures                             6
% 23.42/3.49  EPR                                     10
% 23.42/3.49  Horn                                    26
% 23.42/3.49  unary                                   9
% 23.42/3.49  binary                                  4
% 23.42/3.49  lits                                    72
% 23.42/3.49  lits eq                                 9
% 23.42/3.49  fd_pure                                 0
% 23.42/3.49  fd_pseudo                               0
% 23.42/3.49  fd_cond                                 0
% 23.42/3.49  fd_pseudo_cond                          2
% 23.42/3.49  AC symbols                              0
% 23.42/3.49  
% 23.42/3.49  ------ Input Options Time Limit: Unbounded
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  ------ 
% 23.42/3.49  Current options:
% 23.42/3.49  ------ 
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  ------ Proving...
% 23.42/3.49  
% 23.42/3.49  
% 23.42/3.49  % SZS status Theorem for theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.42/3.49  
% 23.42/3.49  fof(f16,conjecture,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f17,negated_conjecture,(
% 23.42/3.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ((v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) => v1_tex_2(X2,X0)))))),
% 23.42/3.49    inference(negated_conjecture,[],[f16])).
% 23.42/3.49  
% 23.42/3.49  fof(f33,plain,(
% 23.42/3.49    ? [X0] : (? [X1] : (? [X2] : ((~v1_tex_2(X2,X0) & (v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f17])).
% 23.42/3.49  
% 23.42/3.49  fof(f34,plain,(
% 23.42/3.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 23.42/3.49    inference(flattening,[],[f33])).
% 23.42/3.49  
% 23.42/3.49  fof(f45,plain,(
% 23.42/3.49    ( ! [X0,X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) => (~v1_tex_2(sK3,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(sK3,X0))) )),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f44,plain,(
% 23.42/3.49    ( ! [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) => (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(sK2,X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(sK2,X0))) )),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f43,plain,(
% 23.42/3.49    ? [X0] : (? [X1] : (? [X2] : (~v1_tex_2(X2,X0) & v1_tex_2(X1,X0) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tex_2(X2,sK1) & v1_tex_2(X1,sK1) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) & m1_pre_topc(X2,sK1)) & m1_pre_topc(X1,sK1)) & l1_pre_topc(sK1))),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f46,plain,(
% 23.42/3.49    ((~v1_tex_2(sK3,sK1) & v1_tex_2(sK2,sK1) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) & m1_pre_topc(sK3,sK1)) & m1_pre_topc(sK2,sK1)) & l1_pre_topc(sK1)),
% 23.42/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f45,f44,f43])).
% 23.42/3.49  
% 23.42/3.49  fof(f72,plain,(
% 23.42/3.49    m1_pre_topc(sK2,sK1)),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  fof(f12,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f27,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f12])).
% 23.42/3.49  
% 23.42/3.49  fof(f63,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f27])).
% 23.42/3.49  
% 23.42/3.49  fof(f4,axiom,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f37,plain,(
% 23.42/3.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 23.42/3.49    inference(nnf_transformation,[],[f4])).
% 23.42/3.49  
% 23.42/3.49  fof(f53,plain,(
% 23.42/3.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f37])).
% 23.42/3.49  
% 23.42/3.49  fof(f8,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f23,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f8])).
% 23.42/3.49  
% 23.42/3.49  fof(f58,plain,(
% 23.42/3.49    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f23])).
% 23.42/3.49  
% 23.42/3.49  fof(f71,plain,(
% 23.42/3.49    l1_pre_topc(sK1)),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  fof(f73,plain,(
% 23.42/3.49    m1_pre_topc(sK3,sK1)),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  fof(f13,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (u1_struct_0(X1) = u1_struct_0(X2) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f28,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (! [X2] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f13])).
% 23.42/3.49  
% 23.42/3.49  fof(f29,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (! [X2] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(flattening,[],[f28])).
% 23.42/3.49  
% 23.42/3.49  fof(f64,plain,(
% 23.42/3.49    ( ! [X2,X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | u1_struct_0(X1) != u1_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f29])).
% 23.42/3.49  
% 23.42/3.49  fof(f1,axiom,(
% 23.42/3.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f35,plain,(
% 23.42/3.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.42/3.49    inference(nnf_transformation,[],[f1])).
% 23.42/3.49  
% 23.42/3.49  fof(f36,plain,(
% 23.42/3.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 23.42/3.49    inference(flattening,[],[f35])).
% 23.42/3.49  
% 23.42/3.49  fof(f47,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 23.42/3.49    inference(cnf_transformation,[],[f36])).
% 23.42/3.49  
% 23.42/3.49  fof(f78,plain,(
% 23.42/3.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 23.42/3.49    inference(equality_resolution,[],[f47])).
% 23.42/3.49  
% 23.42/3.49  fof(f6,axiom,(
% 23.42/3.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f20,plain,(
% 23.42/3.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f6])).
% 23.42/3.49  
% 23.42/3.49  fof(f21,plain,(
% 23.42/3.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(flattening,[],[f20])).
% 23.42/3.49  
% 23.42/3.49  fof(f56,plain,(
% 23.42/3.49    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f21])).
% 23.42/3.49  
% 23.42/3.49  fof(f7,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f22,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f7])).
% 23.42/3.49  
% 23.42/3.49  fof(f57,plain,(
% 23.42/3.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f22])).
% 23.42/3.49  
% 23.42/3.49  fof(f5,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f18,plain,(
% 23.42/3.49    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f5])).
% 23.42/3.49  
% 23.42/3.49  fof(f19,plain,(
% 23.42/3.49    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(flattening,[],[f18])).
% 23.42/3.49  
% 23.42/3.49  fof(f54,plain,(
% 23.42/3.49    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f19])).
% 23.42/3.49  
% 23.42/3.49  fof(f55,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f21])).
% 23.42/3.49  
% 23.42/3.49  fof(f14,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f30,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f14])).
% 23.42/3.49  
% 23.42/3.49  fof(f31,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(flattening,[],[f30])).
% 23.42/3.49  
% 23.42/3.49  fof(f38,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(nnf_transformation,[],[f31])).
% 23.42/3.49  
% 23.42/3.49  fof(f39,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(rectify,[],[f38])).
% 23.42/3.49  
% 23.42/3.49  fof(f40,plain,(
% 23.42/3.49    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 23.42/3.49    introduced(choice_axiom,[])).
% 23.42/3.49  
% 23.42/3.49  fof(f41,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 23.42/3.49  
% 23.42/3.49  fof(f67,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f41])).
% 23.42/3.49  
% 23.42/3.49  fof(f76,plain,(
% 23.42/3.49    ~v1_tex_2(sK3,sK1)),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  fof(f66,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f41])).
% 23.42/3.49  
% 23.42/3.49  fof(f52,plain,(
% 23.42/3.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f37])).
% 23.42/3.49  
% 23.42/3.49  fof(f49,plain,(
% 23.42/3.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f36])).
% 23.42/3.49  
% 23.42/3.49  fof(f15,axiom,(
% 23.42/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f32,plain,(
% 23.42/3.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(ennf_transformation,[],[f15])).
% 23.42/3.49  
% 23.42/3.49  fof(f42,plain,(
% 23.42/3.49    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.42/3.49    inference(nnf_transformation,[],[f32])).
% 23.42/3.49  
% 23.42/3.49  fof(f69,plain,(
% 23.42/3.49    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f42])).
% 23.42/3.49  
% 23.42/3.49  fof(f80,plain,(
% 23.42/3.49    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 23.42/3.49    inference(equality_resolution,[],[f69])).
% 23.42/3.49  
% 23.42/3.49  fof(f70,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.42/3.49    inference(cnf_transformation,[],[f42])).
% 23.42/3.49  
% 23.42/3.49  fof(f68,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f41])).
% 23.42/3.49  
% 23.42/3.49  fof(f74,plain,(
% 23.42/3.49    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  fof(f11,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f26,plain,(
% 23.42/3.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f11])).
% 23.42/3.49  
% 23.42/3.49  fof(f62,plain,(
% 23.42/3.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f26])).
% 23.42/3.49  
% 23.42/3.49  fof(f9,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f24,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f9])).
% 23.42/3.49  
% 23.42/3.49  fof(f59,plain,(
% 23.42/3.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f24])).
% 23.42/3.49  
% 23.42/3.49  fof(f10,axiom,(
% 23.42/3.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f25,plain,(
% 23.42/3.49    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 23.42/3.49    inference(ennf_transformation,[],[f10])).
% 23.42/3.49  
% 23.42/3.49  fof(f61,plain,(
% 23.42/3.49    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f25])).
% 23.42/3.49  
% 23.42/3.49  fof(f3,axiom,(
% 23.42/3.49    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f51,plain,(
% 23.42/3.49    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f3])).
% 23.42/3.49  
% 23.42/3.49  fof(f2,axiom,(
% 23.42/3.49    ! [X0] : k2_subset_1(X0) = X0),
% 23.42/3.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.42/3.49  
% 23.42/3.49  fof(f50,plain,(
% 23.42/3.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 23.42/3.49    inference(cnf_transformation,[],[f2])).
% 23.42/3.49  
% 23.42/3.49  fof(f65,plain,(
% 23.42/3.49    ( ! [X0,X3,X1] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(cnf_transformation,[],[f41])).
% 23.42/3.49  
% 23.42/3.49  fof(f79,plain,(
% 23.42/3.49    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 23.42/3.49    inference(equality_resolution,[],[f65])).
% 23.42/3.49  
% 23.42/3.49  fof(f75,plain,(
% 23.42/3.49    v1_tex_2(sK2,sK1)),
% 23.42/3.49    inference(cnf_transformation,[],[f46])).
% 23.42/3.49  
% 23.42/3.49  cnf(c_28,negated_conjecture,
% 23.42/3.49      ( m1_pre_topc(sK2,sK1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f72]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2455,plain,
% 23.42/3.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_16,plain,
% 23.42/3.49      ( ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.49      | ~ l1_pre_topc(X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2465,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f53]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2476,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 23.42/3.49      | r1_tarski(X0,X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_11,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | u1_struct_0(k1_pre_topc(X1,X0)) = X0 ),
% 23.42/3.49      inference(cnf_transformation,[],[f58]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2470,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 23.42/3.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3760,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
% 23.42/3.49      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2476,c_2470]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4105,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(X0,u1_struct_0(X1))) = u1_struct_0(X1)
% 23.42/3.49      | m1_pre_topc(X1,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2465,c_3760]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_7953,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))) = u1_struct_0(sK2)
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2455,c_4105]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_29,negated_conjecture,
% 23.42/3.49      ( l1_pre_topc(sK1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_30,plain,
% 23.42/3.49      ( l1_pre_topc(sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8359,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))) = u1_struct_0(sK2) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_7953,c_30]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_27,negated_conjecture,
% 23.42/3.49      ( m1_pre_topc(sK3,sK1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f73]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2456,plain,
% 23.42/3.49      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_7952,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))) = u1_struct_0(sK3)
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2456,c_4105]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8156,plain,
% 23.42/3.49      ( u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))) = u1_struct_0(sK3) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_7952,c_30]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_17,plain,
% 23.42/3.49      ( ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | ~ m1_pre_topc(X2,X1)
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 23.42/3.49      | u1_struct_0(X2) != u1_struct_0(X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2464,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(X1)
% 23.42/3.49      | m1_pre_topc(X1,X2) != iProver_top
% 23.42/3.49      | m1_pre_topc(X0,X2) != iProver_top
% 23.42/3.49      | l1_pre_topc(X2) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8172,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK3))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_8156,c_2464]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8226,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(light_normalisation,[status(thm)],[c_8172,c_8156]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2454,plain,
% 23.42/3.49      ( l1_pre_topc(sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2,plain,
% 23.42/3.49      ( r1_tarski(X0,X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f78]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2478,plain,
% 23.42/3.49      ( r1_tarski(X0,X0) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
% 23.42/3.49      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.42/3.49      | ~ l1_pre_topc(X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f56]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2473,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 23.42/3.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5081,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(X0,X1),X0) = iProver_top
% 23.42/3.49      | r1_tarski(X1,u1_struct_0(X0)) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2476,c_2473]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_10,plain,
% 23.42/3.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2471,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_9995,plain,
% 23.42/3.49      ( r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X1,X0)) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_5081,c_2471]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_10296,plain,
% 23.42/3.49      ( l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2478,c_9995]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_7,plain,
% 23.42/3.49      ( ~ l1_pre_topc(X0)
% 23.42/3.49      | ~ v1_pre_topc(X0)
% 23.42/3.49      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 23.42/3.49      inference(cnf_transformation,[],[f54]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2474,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | v1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_11574,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_10296,c_2474]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2768,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.49      | ~ r1_tarski(X0,u1_struct_0(X1)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2846,plain,
% 23.42/3.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2768]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2848,plain,
% 23.42/3.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2847,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2852,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X0)) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_2847]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_9,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | v1_pre_topc(k1_pre_topc(X1,X0)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f55]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3148,plain,
% 23.42/3.49      ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 23.42/3.49      | ~ l1_pre_topc(X0)
% 23.42/3.49      | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_9]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3149,plain,
% 23.42/3.49      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_3148]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4080,plain,
% 23.42/3.49      ( ~ l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))
% 23.42/3.49      | ~ v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))
% 23.42/3.49      | g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_7]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4081,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top
% 23.42/3.49      | v1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_4080]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3952,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X1,X0)) ),
% 23.42/3.49      inference(resolution,[status(thm)],[c_8,c_10]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4652,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X1,X0)) ),
% 23.42/3.49      inference(resolution,[status(thm)],[c_3952,c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4664,plain,
% 23.42/3.49      ( ~ l1_pre_topc(X0)
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) ),
% 23.42/3.49      inference(resolution,[status(thm)],[c_4652,c_2]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4665,plain,
% 23.42/3.49      ( l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0))) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_4664]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_70719,plain,
% 23.42/3.49      ( l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0)) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_11574,c_2848,c_2852,c_3149,c_4081,c_4665]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_70720,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(X0,u1_struct_0(X0))),u1_pre_topc(k1_pre_topc(X0,u1_struct_0(X0)))) = k1_pre_topc(X0,u1_struct_0(X0))
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_70719]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_70727,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK1))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK1)))) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2454,c_70720]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_19,plain,
% 23.42/3.49      ( v1_tex_2(X0,X1)
% 23.42/3.49      | ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | sK0(X1,X0) = u1_struct_0(X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2462,plain,
% 23.42/3.49      ( sK0(X0,X1) = u1_struct_0(X1)
% 23.42/3.49      | v1_tex_2(X1,X0) = iProver_top
% 23.42/3.49      | m1_pre_topc(X1,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4582,plain,
% 23.42/3.49      ( sK0(sK1,sK3) = u1_struct_0(sK3)
% 23.42/3.49      | v1_tex_2(sK3,sK1) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2456,c_2462]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_24,negated_conjecture,
% 23.42/3.49      ( ~ v1_tex_2(sK3,sK1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f76]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_613,plain,
% 23.42/3.49      ( ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | ~ l1_pre_topc(X1)
% 23.42/3.49      | sK0(X1,X0) = u1_struct_0(X0)
% 23.42/3.49      | sK1 != X1
% 23.42/3.49      | sK3 != X0 ),
% 23.42/3.49      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_614,plain,
% 23.42/3.49      ( ~ m1_pre_topc(sK3,sK1)
% 23.42/3.49      | ~ l1_pre_topc(sK1)
% 23.42/3.49      | sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 23.42/3.49      inference(unflattening,[status(thm)],[c_613]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5856,plain,
% 23.42/3.49      ( sK0(sK1,sK3) = u1_struct_0(sK3) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_4582,c_29,c_27,c_614]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_20,plain,
% 23.42/3.49      ( v1_tex_2(X0,X1)
% 23.42/3.49      | ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.49      | ~ l1_pre_topc(X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2461,plain,
% 23.42/3.49      ( v1_tex_2(X0,X1) = iProver_top
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5859,plain,
% 23.42/3.49      ( v1_tex_2(sK3,sK1) = iProver_top
% 23.42/3.49      | m1_pre_topc(sK3,sK1) != iProver_top
% 23.42/3.49      | m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_5856,c_2461]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_32,plain,
% 23.42/3.49      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_34,plain,
% 23.42/3.49      ( v1_tex_2(sK3,sK1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_24696,plain,
% 23.42/3.49      ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_5859,c_30,c_32,c_34]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_6,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f52]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2475,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.42/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_24701,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_24696,c_2475]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_0,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 23.42/3.49      inference(cnf_transformation,[],[f49]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2479,plain,
% 23.42/3.49      ( X0 = X1
% 23.42/3.49      | r1_tarski(X0,X1) != iProver_top
% 23.42/3.49      | r1_tarski(X1,X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_24956,plain,
% 23.42/3.49      ( u1_struct_0(sK1) = u1_struct_0(sK3)
% 23.42/3.49      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_24701,c_2479]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_23,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X0)) | ~ v1_subset_1(X0,X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f80]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_36,plain,
% 23.42/3.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~ v1_subset_1(sK1,sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_23]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_22,plain,
% 23.42/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.42/3.49      | v1_subset_1(X0,X1)
% 23.42/3.49      | X0 = X1 ),
% 23.42/3.49      inference(cnf_transformation,[],[f70]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_39,plain,
% 23.42/3.49      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
% 23.42/3.49      | v1_subset_1(sK1,sK1)
% 23.42/3.49      | sK1 = sK1 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_22]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_86,plain,
% 23.42/3.49      ( m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~ r1_tarski(sK1,sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_93,plain,
% 23.42/3.49      ( r1_tarski(sK1,sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1777,plain,
% 23.42/3.49      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.42/3.49      theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1788,plain,
% 23.42/3.49      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1777]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_18,plain,
% 23.42/3.49      ( v1_tex_2(X0,X1)
% 23.42/3.49      | ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | ~ v1_subset_1(sK0(X1,X0),u1_struct_0(X1))
% 23.42/3.49      | ~ l1_pre_topc(X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f68]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2463,plain,
% 23.42/3.49      ( v1_tex_2(X0,X1) = iProver_top
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | v1_subset_1(sK0(X1,X0),u1_struct_0(X1)) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5866,plain,
% 23.42/3.49      ( v1_tex_2(sK3,sK1) = iProver_top
% 23.42/3.49      | m1_pre_topc(sK3,sK1) != iProver_top
% 23.42/3.49      | v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_5856,c_2463]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5893,plain,
% 23.42/3.49      ( v1_tex_2(sK3,sK1)
% 23.42/3.49      | ~ m1_pre_topc(sK3,sK1)
% 23.42/3.49      | ~ v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1))
% 23.42/3.49      | ~ l1_pre_topc(sK1) ),
% 23.42/3.49      inference(predicate_to_equality_rev,[status(thm)],[c_5866]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_10813,plain,
% 23.42/3.49      ( ~ m1_pre_topc(sK3,X0)
% 23.42/3.49      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 23.42/3.49      | ~ l1_pre_topc(X0) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_10815,plain,
% 23.42/3.49      ( ~ m1_pre_topc(sK3,sK1)
% 23.42/3.49      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1))
% 23.42/3.49      | ~ l1_pre_topc(sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_10813]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1772,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3222,plain,
% 23.42/3.49      ( X0 != X1 | u1_struct_0(X2) != X1 | u1_struct_0(X2) = X0 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1772]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4209,plain,
% 23.42/3.49      ( X0 != u1_struct_0(X1)
% 23.42/3.49      | u1_struct_0(X2) = X0
% 23.42/3.49      | u1_struct_0(X2) != u1_struct_0(X1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_3222]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_7880,plain,
% 23.42/3.49      ( u1_struct_0(X0) != u1_struct_0(X1)
% 23.42/3.49      | u1_struct_0(X2) != u1_struct_0(X1)
% 23.42/3.49      | u1_struct_0(X0) = u1_struct_0(X2) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_4209]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_17335,plain,
% 23.42/3.49      ( u1_struct_0(X0) != u1_struct_0(X1)
% 23.42/3.49      | u1_struct_0(X0) = u1_struct_0(sK3)
% 23.42/3.49      | u1_struct_0(sK3) != u1_struct_0(X1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_7880]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_17339,plain,
% 23.42/3.49      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 23.42/3.49      | u1_struct_0(sK1) = u1_struct_0(sK3)
% 23.42/3.49      | u1_struct_0(sK3) != u1_struct_0(sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_17335]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_216,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 23.42/3.49      inference(prop_impl,[status(thm)],[c_5]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_217,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_216]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_265,plain,
% 23.42/3.49      ( v1_subset_1(X0,X1) | ~ r1_tarski(X0,X1) | X0 = X1 ),
% 23.42/3.49      inference(bin_hyper_res,[status(thm)],[c_22,c_217]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3208,plain,
% 23.42/3.49      ( v1_subset_1(u1_struct_0(X0),X1)
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(X0),X1)
% 23.42/3.49      | u1_struct_0(X0) = X1 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_265]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4186,plain,
% 23.42/3.49      ( v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.49      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_3208]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_21071,plain,
% 23.42/3.49      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(X0))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(X0))
% 23.42/3.49      | u1_struct_0(sK3) = u1_struct_0(X0) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_4186]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_21075,plain,
% 23.42/3.49      ( v1_subset_1(u1_struct_0(sK3),u1_struct_0(sK1))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK1))
% 23.42/3.49      | u1_struct_0(sK3) = u1_struct_0(sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_21071]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_26735,plain,
% 23.42/3.49      ( u1_struct_0(sK1) = u1_struct_0(sK3) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_24956,c_29,c_27,c_24,c_36,c_39,c_86,c_93,c_1788,
% 23.42/3.49                 c_5893,c_10815,c_17339,c_21075]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_70874,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)))) = k1_pre_topc(sK1,u1_struct_0(sK3)) ),
% 23.42/3.49      inference(light_normalisation,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_70727,c_8156,c_26735]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78777,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(light_normalisation,[status(thm)],[c_8226,c_70874]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78789,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | u1_struct_0(sK3) != u1_struct_0(sK2)
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_8359,c_78777]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78903,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | u1_struct_0(sK3) != u1_struct_0(sK2)
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(light_normalisation,[status(thm)],[c_78789,c_8359]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_27000,plain,
% 23.42/3.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_26735,c_2465]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_29604,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top
% 23.42/3.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_27000,c_30]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_29605,plain,
% 23.42/3.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK3)) = iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_29604]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_26984,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
% 23.42/3.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_26735,c_2473]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_34457,plain,
% 23.42/3.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_26984,c_30]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_34458,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
% 23.42/3.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_34457]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_34465,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,X0),sK1) = iProver_top
% 23.42/3.49      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2476,c_34458]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8375,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(k1_pre_topc(sK1,u1_struct_0(sK2))),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK2)
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_8359,c_2464]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8429,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK2)
% 23.42/3.49      | m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X1) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(light_normalisation,[status(thm)],[c_8375,c_8359]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78988,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(sK2,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(equality_resolution,[status(thm)],[c_8429]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_26,negated_conjecture,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 23.42/3.49      inference(cnf_transformation,[],[f74]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78993,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(sK2,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(light_normalisation,[status(thm)],[c_78988,c_26]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_79296,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 23.42/3.49      | m1_pre_topc(sK2,sK1) != iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_34465,c_78993]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_31,plain,
% 23.42/3.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_79680,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top
% 23.42/3.49      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_79296,c_30,c_31]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_79681,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 23.42/3.49      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK3)) != iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_79680]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_79687,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
% 23.42/3.49      | m1_pre_topc(sK2,sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_29605,c_79681]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_79701,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)))) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_79687,c_31]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_86585,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | u1_struct_0(sK3) != u1_struct_0(sK2)
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK2)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(demodulation,[status(thm)],[c_78903,c_79701]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_24702,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK1) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_24696,c_2473]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78799,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
% 23.42/3.49      | m1_pre_topc(sK3,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(equality_resolution,[status(thm)],[c_78777]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78935,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3))
% 23.42/3.49      | m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK1) != iProver_top
% 23.42/3.49      | m1_pre_topc(sK3,sK1) != iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_78799]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_86594,plain,
% 23.42/3.49      ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k1_pre_topc(sK1,u1_struct_0(sK3)) ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_86585,c_30,c_32,c_24702,c_78935]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_15,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2466,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X0) = iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_12,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X1)
% 23.42/3.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 23.42/3.49      | ~ l1_pre_topc(X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f59]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2469,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X1) = iProver_top
% 23.42/3.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4880,plain,
% 23.42/3.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.42/3.49      | m1_pre_topc(X0,sK2) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK2) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_26,c_2469]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2748,plain,
% 23.42/3.49      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 23.42/3.49      inference(resolution,[status(thm)],[c_10,c_28]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2749,plain,
% 23.42/3.49      ( l1_pre_topc(sK2) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_2748]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5305,plain,
% 23.42/3.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 23.42/3.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_4880,c_30,c_2749]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5306,plain,
% 23.42/3.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top
% 23.42/3.49      | m1_pre_topc(X0,sK2) = iProver_top ),
% 23.42/3.49      inference(renaming,[status(thm)],[c_5305]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5314,plain,
% 23.42/3.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top
% 23.42/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_2466,c_5306]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_13,plain,
% 23.42/3.49      ( ~ m1_pre_topc(X0,X1)
% 23.42/3.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 23.42/3.49      | ~ l1_pre_topc(X1) ),
% 23.42/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2468,plain,
% 23.42/3.49      ( m1_pre_topc(X0,X1) != iProver_top
% 23.42/3.49      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 23.42/3.49      | l1_pre_topc(X1) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4812,plain,
% 23.42/3.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),X0) = iProver_top
% 23.42/3.49      | m1_pre_topc(sK2,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_26,c_2468]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5129,plain,
% 23.42/3.49      ( m1_pre_topc(sK2,X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top
% 23.42/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_4812,c_2471]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5166,plain,
% 23.42/3.49      ( m1_pre_topc(sK2,sK1) != iProver_top
% 23.42/3.49      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5129]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5337,plain,
% 23.42/3.49      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK2) = iProver_top ),
% 23.42/3.49      inference(global_propositional_subsumption,
% 23.42/3.49                [status(thm)],
% 23.42/3.49                [c_5314,c_30,c_31,c_5166]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_86683,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),sK2) = iProver_top ),
% 23.42/3.49      inference(demodulation,[status(thm)],[c_86594,c_5337]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_8168,plain,
% 23.42/3.49      ( m1_pre_topc(k1_pre_topc(sK1,u1_struct_0(sK3)),X0) != iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(sK3),u1_struct_0(X0)) = iProver_top
% 23.42/3.49      | l1_pre_topc(X0) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_8156,c_2465]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_92099,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) = iProver_top
% 23.42/3.49      | l1_pre_topc(sK2) != iProver_top ),
% 23.42/3.49      inference(superposition,[status(thm)],[c_86683,c_8168]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1773,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.42/3.49      theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_2859,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,X1)
% 23.42/3.49      | r1_tarski(X2,u1_struct_0(X3))
% 23.42/3.49      | X2 != X0
% 23.42/3.49      | u1_struct_0(X3) != X1 ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1773]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_3218,plain,
% 23.42/3.49      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 23.42/3.49      | r1_tarski(X2,u1_struct_0(X3))
% 23.42/3.49      | X2 != X0
% 23.42/3.49      | u1_struct_0(X3) != u1_struct_0(X1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_2859]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4542,plain,
% 23.42/3.49      ( r1_tarski(X0,u1_struct_0(X1))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
% 23.42/3.49      | X0 != u1_struct_0(X2)
% 23.42/3.49      | u1_struct_0(X1) != u1_struct_0(X3) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_3218]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_9130,plain,
% 23.42/3.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.49      | r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
% 23.42/3.49      | u1_struct_0(X3) != u1_struct_0(X1)
% 23.42/3.49      | u1_struct_0(X2) != u1_struct_0(X0) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_4542]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_18891,plain,
% 23.42/3.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.49      | r1_tarski(u1_struct_0(X2),u1_struct_0(sK2))
% 23.42/3.49      | u1_struct_0(X2) != u1_struct_0(X0)
% 23.42/3.49      | u1_struct_0(sK2) != u1_struct_0(X1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_9130]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_32586,plain,
% 23.42/3.49      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 23.42/3.49      | r1_tarski(u1_struct_0(X1),u1_struct_0(sK2))
% 23.42/3.49      | u1_struct_0(X1) != u1_struct_0(X0)
% 23.42/3.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_18891]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78386,plain,
% 23.42/3.49      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
% 23.42/3.49      | ~ r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2))
% 23.42/3.49      | u1_struct_0(X0) != u1_struct_0(sK3)
% 23.42/3.49      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_32586]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78394,plain,
% 23.42/3.49      ( u1_struct_0(X0) != u1_struct_0(sK3)
% 23.42/3.49      | u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.42/3.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) = iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.42/3.49      inference(predicate_to_equality,[status(thm)],[c_78386]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_78396,plain,
% 23.42/3.49      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 23.42/3.49      | u1_struct_0(sK1) != u1_struct_0(sK3)
% 23.42/3.49      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top
% 23.42/3.49      | r1_tarski(u1_struct_0(sK3),u1_struct_0(sK2)) != iProver_top ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_78394]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_4,plain,
% 23.42/3.49      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 23.42/3.49      inference(cnf_transformation,[],[f51]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_23839,plain,
% 23.42/3.49      ( ~ v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_4]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_1774,plain,
% 23.42/3.49      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.42/3.49      theory(equality) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5072,plain,
% 23.42/3.49      ( v1_subset_1(X0,X1)
% 23.42/3.49      | ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.49      | X0 != u1_struct_0(sK2)
% 23.42/3.49      | X1 != u1_struct_0(sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_1774]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_5506,plain,
% 23.42/3.49      ( v1_subset_1(X0,u1_struct_0(X1))
% 23.42/3.49      | ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.49      | X0 != u1_struct_0(sK2)
% 23.42/3.49      | u1_struct_0(X1) != u1_struct_0(sK1) ),
% 23.42/3.49      inference(instantiation,[status(thm)],[c_5072]) ).
% 23.42/3.49  
% 23.42/3.49  cnf(c_13821,plain,
% 23.42/3.50      ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(X0))
% 23.42/3.50      | u1_struct_0(X0) != u1_struct_0(sK1)
% 23.42/3.50      | k2_subset_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_5506]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_23838,plain,
% 23.42/3.50      ( ~ v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | v1_subset_1(k2_subset_1(u1_struct_0(sK2)),u1_struct_0(sK2))
% 23.42/3.50      | u1_struct_0(sK2) != u1_struct_0(sK1)
% 23.42/3.50      | k2_subset_1(u1_struct_0(sK2)) != u1_struct_0(sK2) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_13821]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_4689,plain,
% 23.42/3.50      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 23.42/3.50      | ~ r1_tarski(u1_struct_0(X1),X0)
% 23.42/3.50      | X0 = u1_struct_0(X1) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_0]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_8123,plain,
% 23.42/3.50      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.50      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
% 23.42/3.50      | u1_struct_0(X0) = u1_struct_0(X1) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_4689]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_22420,plain,
% 23.42/3.50      ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
% 23.42/3.50      | u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_8123]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_22423,plain,
% 23.42/3.50      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 23.42/3.50      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 23.42/3.50      | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top ),
% 23.42/3.50      inference(predicate_to_equality,[status(thm)],[c_22420]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_1771,plain,( X0 = X0 ),theory(equality) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_10506,plain,
% 23.42/3.50      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_1771]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_3,plain,
% 23.42/3.50      ( k2_subset_1(X0) = X0 ),
% 23.42/3.50      inference(cnf_transformation,[],[f50]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_4699,plain,
% 23.42/3.50      ( k2_subset_1(u1_struct_0(X0)) = u1_struct_0(X0) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_3]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_7123,plain,
% 23.42/3.50      ( k2_subset_1(u1_struct_0(sK2)) = u1_struct_0(sK2) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_4699]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_3590,plain,
% 23.42/3.50      ( ~ m1_pre_topc(sK2,sK1)
% 23.42/3.50      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | ~ l1_pre_topc(sK1) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_16]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_3591,plain,
% 23.42/3.50      ( m1_pre_topc(sK2,sK1) != iProver_top
% 23.42/3.50      | r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 23.42/3.50      | l1_pre_topc(sK1) != iProver_top ),
% 23.42/3.50      inference(predicate_to_equality,[status(thm)],[c_3590]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_2856,plain,
% 23.42/3.50      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.50      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_2768]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_3457,plain,
% 23.42/3.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 23.42/3.50      | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 23.42/3.50      inference(instantiation,[status(thm)],[c_2856]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_21,plain,
% 23.42/3.50      ( ~ v1_tex_2(X0,X1)
% 23.42/3.50      | ~ m1_pre_topc(X0,X1)
% 23.42/3.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.50      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.50      | ~ l1_pre_topc(X1) ),
% 23.42/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_25,negated_conjecture,
% 23.42/3.50      ( v1_tex_2(sK2,sK1) ),
% 23.42/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_632,plain,
% 23.42/3.50      ( ~ m1_pre_topc(X0,X1)
% 23.42/3.50      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 23.42/3.50      | v1_subset_1(u1_struct_0(X0),u1_struct_0(X1))
% 23.42/3.50      | ~ l1_pre_topc(X1)
% 23.42/3.50      | sK2 != X0
% 23.42/3.50      | sK1 != X1 ),
% 23.42/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_633,plain,
% 23.42/3.50      ( ~ m1_pre_topc(sK2,sK1)
% 23.42/3.50      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 23.42/3.50      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | ~ l1_pre_topc(sK1) ),
% 23.42/3.50      inference(unflattening,[status(thm)],[c_632]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_635,plain,
% 23.42/3.50      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1))
% 23.42/3.50      | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 23.42/3.50      inference(global_propositional_subsumption,
% 23.42/3.50                [status(thm)],
% 23.42/3.50                [c_633,c_29,c_28]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(c_636,plain,
% 23.42/3.50      ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 23.42/3.50      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) ),
% 23.42/3.50      inference(renaming,[status(thm)],[c_635]) ).
% 23.42/3.50  
% 23.42/3.50  cnf(contradiction,plain,
% 23.42/3.50      ( $false ),
% 23.42/3.50      inference(minisat,
% 23.42/3.50                [status(thm)],
% 23.42/3.50                [c_92099,c_78396,c_23839,c_23838,c_22423,c_21075,c_17339,
% 23.42/3.50                 c_10815,c_10506,c_7123,c_5893,c_3591,c_3590,c_3457,
% 23.42/3.50                 c_2749,c_1788,c_636,c_93,c_86,c_39,c_36,c_24,c_27,c_31,
% 23.42/3.50                 c_28,c_30,c_29]) ).
% 23.42/3.50  
% 23.42/3.50  
% 23.42/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.42/3.50  
% 23.42/3.50  ------                               Statistics
% 23.42/3.50  
% 23.42/3.50  ------ Selected
% 23.42/3.50  
% 23.42/3.50  total_time:                             2.748
% 23.42/3.50  
%------------------------------------------------------------------------------
