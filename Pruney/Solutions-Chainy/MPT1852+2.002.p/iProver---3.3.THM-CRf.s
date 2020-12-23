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
% DateTime   : Thu Dec  3 12:25:33 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :  228 (1220 expanded)
%              Number of clauses        :  159 ( 469 expanded)
%              Number of leaves         :   23 ( 259 expanded)
%              Depth                    :   28
%              Number of atoms          :  747 (4775 expanded)
%              Number of equality atoms :  259 (1139 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ? [X1] :
              ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ( v3_tdlat_3(X0)
          | ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
            & r2_hidden(sK0(X0),u1_pre_topc(X0))
            & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v3_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).

fof(f61,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
     => ( ~ v3_tdlat_3(sK2)
        & v3_tdlat_3(X0)
        & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & l1_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tdlat_3(X1)
            & v3_tdlat_3(X0)
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(sK1)
          & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f42,f41])).

fof(f67,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f64,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f68,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_799,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2499,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
    | X2 != X1
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_799])).

cnf(c_2892,plain,
    ( ~ r2_hidden(k6_subset_1(X0,X1),X2)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X3)
    | X3 != X2
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2499])).

cnf(c_6515,plain,
    ( ~ r2_hidden(k6_subset_1(X0,sK0(sK2)),X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
    | X2 != X1
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2892])).

cnf(c_9737,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
    | X2 != X1
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6515])).

cnf(c_16918,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X1)
    | X1 != u1_pre_topc(X0)
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_9737])).

cnf(c_23043,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(X0) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_16918])).

cnf(c_23045,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_23043])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2789,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3961,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_2789])).

cnf(c_5703,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
    | m1_subset_1(k6_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_3961])).

cnf(c_16905,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(instantiation,[status(thm)],[c_5703])).

cnf(c_16907,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_16905])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_12665,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_12682,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_12665])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_136,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X2,X0)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14,c_10])).

cnf(c_137,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_136])).

cnf(c_12489,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | v3_pre_topc(sK0(sK2),X0)
    | ~ v3_pre_topc(sK0(sK2),sK2)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_12491,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | v3_pre_topc(sK0(sK2),sK1)
    | ~ v3_pre_topc(sK0(sK2),sK2)
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12489])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1333,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_23,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_141,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_8])).

cnf(c_142,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_141])).

cnf(c_1323,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_142])).

cnf(c_1715,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1323])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_26,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1894,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1715,c_26])).

cnf(c_1895,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_1894])).

cnf(c_11,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1335,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2300,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1335])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_27,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2422,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_27])).

cnf(c_2423,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_2422])).

cnf(c_2428,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_2423])).

cnf(c_36,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1612,plain,
    ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1613,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1612])).

cnf(c_1615,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_1717,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1715])).

cnf(c_2559,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2428,c_26,c_27,c_38,c_1615,c_1717])).

cnf(c_19,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1330,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v3_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2301,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1335])).

cnf(c_2408,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2301,c_26])).

cnf(c_2409,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2408])).

cnf(c_2414,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_2409])).

cnf(c_2481,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2414,c_27])).

cnf(c_2482,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2481])).

cnf(c_2487,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1333,c_2482])).

cnf(c_2628,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2487,c_27])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1334,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1342,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2125,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1334,c_1342])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1345,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3001,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_1345])).

cnf(c_3504,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2125,c_3001])).

cnf(c_52,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4062,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3504,c_52])).

cnf(c_4063,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_4062])).

cnf(c_4069,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2628,c_4063])).

cnf(c_4592,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4069,c_26,c_27,c_38,c_1615,c_1717])).

cnf(c_1336,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4616,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4592,c_1336])).

cnf(c_7516,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v3_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1330,c_4616])).

cnf(c_21,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_29,plain,
    ( v3_tdlat_3(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8056,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7516,c_27,c_29])).

cnf(c_8057,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8056])).

cnf(c_8066,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8057,c_1336])).

cnf(c_9519,plain,
    ( l1_pre_topc(X1) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8066,c_52])).

cnf(c_9520,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_9519])).

cnf(c_9527,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2559,c_9520])).

cnf(c_380,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_381,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_382,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_11050,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9527,c_27,c_382])).

cnf(c_7,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1339,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4632,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4592,c_1339])).

cnf(c_2577,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2578,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2577])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1343,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2753,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1343,c_1339])).

cnf(c_4629,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4592,c_2753])).

cnf(c_6022,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4632,c_26,c_2578,c_4629])).

cnf(c_6023,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6022])).

cnf(c_11059,plain,
    ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11050,c_6023])).

cnf(c_11072,plain,
    ( ~ v3_pre_topc(sK0(sK2),sK1)
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11059])).

cnf(c_798,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2198,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | k1_zfmisc_1(u1_struct_0(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_2519,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),X2)
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X3)) != X2 ),
    inference(instantiation,[status(thm)],[c_2198])).

cnf(c_2907,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_6514,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2907])).

cnf(c_9727,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_6514])).

cnf(c_9729,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9727])).

cnf(c_2913,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X2))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X3)) != k1_zfmisc_1(X2) ),
    inference(instantiation,[status(thm)],[c_2519])).

cnf(c_4757,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_2913])).

cnf(c_9671,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_4757])).

cnf(c_9675,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9671])).

cnf(c_806,plain,
    ( X0 != X1
    | X2 != X3
    | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_3812,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
    | sK0(sK2) != X1
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_806])).

cnf(c_5360,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_3812])).

cnf(c_7136,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_5360])).

cnf(c_7137,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7136])).

cnf(c_795,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3915,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_795])).

cnf(c_3916,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3915])).

cnf(c_6,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3755,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3757,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3755])).

cnf(c_3531,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3533,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_797,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2025,plain,
    ( u1_struct_0(sK2) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_797])).

cnf(c_2556,plain,
    ( u1_struct_0(sK2) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_2557,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_2488,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2487])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1978,plain,
    ( r1_tarski(sK0(sK2),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1676,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X0,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1917,plain,
    ( v3_pre_topc(sK0(sK2),sK2)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_1636,plain,
    ( ~ r1_tarski(X0,sK0(sK2))
    | ~ r1_tarski(sK0(sK2),X0)
    | sK0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1883,plain,
    ( ~ r1_tarski(sK0(sK2),sK0(sK2))
    | sK0(sK2) = sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_1716,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1715])).

cnf(c_1718,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1716])).

cnf(c_1614,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1612])).

cnf(c_1410,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_137])).

cnf(c_1412,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_1387,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_800,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_810,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_17,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_402,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_21])).

cnf(c_403,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_18,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_391,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_21])).

cnf(c_392,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_73,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_69,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_50,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_22,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23045,c_16907,c_12682,c_12491,c_11072,c_9729,c_9675,c_7137,c_4069,c_3916,c_3757,c_3533,c_2557,c_2488,c_1978,c_1917,c_1883,c_1718,c_1717,c_1615,c_1614,c_1412,c_1387,c_810,c_403,c_392,c_381,c_73,c_69,c_50,c_38,c_37,c_22,c_27,c_24,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:15:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.85/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.49  
% 7.85/1.49  ------  iProver source info
% 7.85/1.49  
% 7.85/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.49  git: non_committed_changes: false
% 7.85/1.49  git: last_make_outside_of_git: false
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options
% 7.85/1.49  
% 7.85/1.49  --out_options                           all
% 7.85/1.49  --tptp_safe_out                         true
% 7.85/1.49  --problem_path                          ""
% 7.85/1.49  --include_path                          ""
% 7.85/1.49  --clausifier                            res/vclausify_rel
% 7.85/1.49  --clausifier_options                    ""
% 7.85/1.49  --stdin                                 false
% 7.85/1.49  --stats_out                             all
% 7.85/1.49  
% 7.85/1.49  ------ General Options
% 7.85/1.49  
% 7.85/1.49  --fof                                   false
% 7.85/1.49  --time_out_real                         305.
% 7.85/1.49  --time_out_virtual                      -1.
% 7.85/1.49  --symbol_type_check                     false
% 7.85/1.49  --clausify_out                          false
% 7.85/1.49  --sig_cnt_out                           false
% 7.85/1.49  --trig_cnt_out                          false
% 7.85/1.49  --trig_cnt_out_tolerance                1.
% 7.85/1.49  --trig_cnt_out_sk_spl                   false
% 7.85/1.49  --abstr_cl_out                          false
% 7.85/1.49  
% 7.85/1.49  ------ Global Options
% 7.85/1.49  
% 7.85/1.49  --schedule                              default
% 7.85/1.49  --add_important_lit                     false
% 7.85/1.49  --prop_solver_per_cl                    1000
% 7.85/1.49  --min_unsat_core                        false
% 7.85/1.49  --soft_assumptions                      false
% 7.85/1.49  --soft_lemma_size                       3
% 7.85/1.49  --prop_impl_unit_size                   0
% 7.85/1.49  --prop_impl_unit                        []
% 7.85/1.49  --share_sel_clauses                     true
% 7.85/1.49  --reset_solvers                         false
% 7.85/1.49  --bc_imp_inh                            [conj_cone]
% 7.85/1.49  --conj_cone_tolerance                   3.
% 7.85/1.49  --extra_neg_conj                        none
% 7.85/1.49  --large_theory_mode                     true
% 7.85/1.49  --prolific_symb_bound                   200
% 7.85/1.49  --lt_threshold                          2000
% 7.85/1.49  --clause_weak_htbl                      true
% 7.85/1.49  --gc_record_bc_elim                     false
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing Options
% 7.85/1.49  
% 7.85/1.49  --preprocessing_flag                    true
% 7.85/1.49  --time_out_prep_mult                    0.1
% 7.85/1.49  --splitting_mode                        input
% 7.85/1.49  --splitting_grd                         true
% 7.85/1.49  --splitting_cvd                         false
% 7.85/1.49  --splitting_cvd_svl                     false
% 7.85/1.49  --splitting_nvd                         32
% 7.85/1.49  --sub_typing                            true
% 7.85/1.49  --prep_gs_sim                           true
% 7.85/1.49  --prep_unflatten                        true
% 7.85/1.49  --prep_res_sim                          true
% 7.85/1.49  --prep_upred                            true
% 7.85/1.49  --prep_sem_filter                       exhaustive
% 7.85/1.49  --prep_sem_filter_out                   false
% 7.85/1.49  --pred_elim                             true
% 7.85/1.49  --res_sim_input                         true
% 7.85/1.49  --eq_ax_congr_red                       true
% 7.85/1.49  --pure_diseq_elim                       true
% 7.85/1.49  --brand_transform                       false
% 7.85/1.49  --non_eq_to_eq                          false
% 7.85/1.49  --prep_def_merge                        true
% 7.85/1.49  --prep_def_merge_prop_impl              false
% 7.85/1.49  --prep_def_merge_mbd                    true
% 7.85/1.49  --prep_def_merge_tr_red                 false
% 7.85/1.49  --prep_def_merge_tr_cl                  false
% 7.85/1.49  --smt_preprocessing                     true
% 7.85/1.49  --smt_ac_axioms                         fast
% 7.85/1.49  --preprocessed_out                      false
% 7.85/1.49  --preprocessed_stats                    false
% 7.85/1.49  
% 7.85/1.49  ------ Abstraction refinement Options
% 7.85/1.49  
% 7.85/1.49  --abstr_ref                             []
% 7.85/1.49  --abstr_ref_prep                        false
% 7.85/1.49  --abstr_ref_until_sat                   false
% 7.85/1.49  --abstr_ref_sig_restrict                funpre
% 7.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.49  --abstr_ref_under                       []
% 7.85/1.49  
% 7.85/1.49  ------ SAT Options
% 7.85/1.49  
% 7.85/1.49  --sat_mode                              false
% 7.85/1.49  --sat_fm_restart_options                ""
% 7.85/1.49  --sat_gr_def                            false
% 7.85/1.49  --sat_epr_types                         true
% 7.85/1.49  --sat_non_cyclic_types                  false
% 7.85/1.49  --sat_finite_models                     false
% 7.85/1.49  --sat_fm_lemmas                         false
% 7.85/1.49  --sat_fm_prep                           false
% 7.85/1.49  --sat_fm_uc_incr                        true
% 7.85/1.49  --sat_out_model                         small
% 7.85/1.49  --sat_out_clauses                       false
% 7.85/1.49  
% 7.85/1.49  ------ QBF Options
% 7.85/1.49  
% 7.85/1.49  --qbf_mode                              false
% 7.85/1.49  --qbf_elim_univ                         false
% 7.85/1.49  --qbf_dom_inst                          none
% 7.85/1.49  --qbf_dom_pre_inst                      false
% 7.85/1.49  --qbf_sk_in                             false
% 7.85/1.49  --qbf_pred_elim                         true
% 7.85/1.49  --qbf_split                             512
% 7.85/1.49  
% 7.85/1.49  ------ BMC1 Options
% 7.85/1.49  
% 7.85/1.49  --bmc1_incremental                      false
% 7.85/1.49  --bmc1_axioms                           reachable_all
% 7.85/1.49  --bmc1_min_bound                        0
% 7.85/1.49  --bmc1_max_bound                        -1
% 7.85/1.49  --bmc1_max_bound_default                -1
% 7.85/1.49  --bmc1_symbol_reachability              true
% 7.85/1.49  --bmc1_property_lemmas                  false
% 7.85/1.49  --bmc1_k_induction                      false
% 7.85/1.49  --bmc1_non_equiv_states                 false
% 7.85/1.49  --bmc1_deadlock                         false
% 7.85/1.49  --bmc1_ucm                              false
% 7.85/1.49  --bmc1_add_unsat_core                   none
% 7.85/1.49  --bmc1_unsat_core_children              false
% 7.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.49  --bmc1_out_stat                         full
% 7.85/1.49  --bmc1_ground_init                      false
% 7.85/1.49  --bmc1_pre_inst_next_state              false
% 7.85/1.49  --bmc1_pre_inst_state                   false
% 7.85/1.49  --bmc1_pre_inst_reach_state             false
% 7.85/1.49  --bmc1_out_unsat_core                   false
% 7.85/1.49  --bmc1_aig_witness_out                  false
% 7.85/1.49  --bmc1_verbose                          false
% 7.85/1.49  --bmc1_dump_clauses_tptp                false
% 7.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.49  --bmc1_dump_file                        -
% 7.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.49  --bmc1_ucm_extend_mode                  1
% 7.85/1.49  --bmc1_ucm_init_mode                    2
% 7.85/1.49  --bmc1_ucm_cone_mode                    none
% 7.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.49  --bmc1_ucm_relax_model                  4
% 7.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.49  --bmc1_ucm_layered_model                none
% 7.85/1.49  --bmc1_ucm_max_lemma_size               10
% 7.85/1.49  
% 7.85/1.49  ------ AIG Options
% 7.85/1.49  
% 7.85/1.49  --aig_mode                              false
% 7.85/1.49  
% 7.85/1.49  ------ Instantiation Options
% 7.85/1.49  
% 7.85/1.49  --instantiation_flag                    true
% 7.85/1.49  --inst_sos_flag                         true
% 7.85/1.49  --inst_sos_phase                        true
% 7.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel_side                     num_symb
% 7.85/1.49  --inst_solver_per_active                1400
% 7.85/1.49  --inst_solver_calls_frac                1.
% 7.85/1.49  --inst_passive_queue_type               priority_queues
% 7.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.49  --inst_passive_queues_freq              [25;2]
% 7.85/1.49  --inst_dismatching                      true
% 7.85/1.49  --inst_eager_unprocessed_to_passive     true
% 7.85/1.49  --inst_prop_sim_given                   true
% 7.85/1.49  --inst_prop_sim_new                     false
% 7.85/1.49  --inst_subs_new                         false
% 7.85/1.49  --inst_eq_res_simp                      false
% 7.85/1.49  --inst_subs_given                       false
% 7.85/1.49  --inst_orphan_elimination               true
% 7.85/1.49  --inst_learning_loop_flag               true
% 7.85/1.49  --inst_learning_start                   3000
% 7.85/1.49  --inst_learning_factor                  2
% 7.85/1.49  --inst_start_prop_sim_after_learn       3
% 7.85/1.49  --inst_sel_renew                        solver
% 7.85/1.49  --inst_lit_activity_flag                true
% 7.85/1.49  --inst_restr_to_given                   false
% 7.85/1.49  --inst_activity_threshold               500
% 7.85/1.49  --inst_out_proof                        true
% 7.85/1.49  
% 7.85/1.49  ------ Resolution Options
% 7.85/1.49  
% 7.85/1.49  --resolution_flag                       true
% 7.85/1.49  --res_lit_sel                           adaptive
% 7.85/1.49  --res_lit_sel_side                      none
% 7.85/1.49  --res_ordering                          kbo
% 7.85/1.49  --res_to_prop_solver                    active
% 7.85/1.49  --res_prop_simpl_new                    false
% 7.85/1.49  --res_prop_simpl_given                  true
% 7.85/1.49  --res_passive_queue_type                priority_queues
% 7.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.49  --res_passive_queues_freq               [15;5]
% 7.85/1.49  --res_forward_subs                      full
% 7.85/1.49  --res_backward_subs                     full
% 7.85/1.49  --res_forward_subs_resolution           true
% 7.85/1.49  --res_backward_subs_resolution          true
% 7.85/1.49  --res_orphan_elimination                true
% 7.85/1.49  --res_time_limit                        2.
% 7.85/1.49  --res_out_proof                         true
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Options
% 7.85/1.49  
% 7.85/1.49  --superposition_flag                    true
% 7.85/1.49  --sup_passive_queue_type                priority_queues
% 7.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.85/1.49  --demod_completeness_check              fast
% 7.85/1.49  --demod_use_ground                      true
% 7.85/1.49  --sup_to_prop_solver                    passive
% 7.85/1.49  --sup_prop_simpl_new                    true
% 7.85/1.49  --sup_prop_simpl_given                  true
% 7.85/1.49  --sup_fun_splitting                     true
% 7.85/1.49  --sup_smt_interval                      50000
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Simplification Setup
% 7.85/1.49  
% 7.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_immed_triv                        [TrivRules]
% 7.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_bw_main                     []
% 7.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_input_bw                          []
% 7.85/1.49  
% 7.85/1.49  ------ Combination Options
% 7.85/1.49  
% 7.85/1.49  --comb_res_mult                         3
% 7.85/1.49  --comb_sup_mult                         2
% 7.85/1.49  --comb_inst_mult                        10
% 7.85/1.49  
% 7.85/1.49  ------ Debug Options
% 7.85/1.49  
% 7.85/1.49  --dbg_backtrace                         false
% 7.85/1.49  --dbg_dump_prop_clauses                 false
% 7.85/1.49  --dbg_dump_prop_clauses_file            -
% 7.85/1.49  --dbg_out_stat                          false
% 7.85/1.49  ------ Parsing...
% 7.85/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.49  ------ Proving...
% 7.85/1.49  ------ Problem Properties 
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  clauses                                 24
% 7.85/1.49  conjectures                             5
% 7.85/1.49  EPR                                     8
% 7.85/1.49  Horn                                    22
% 7.85/1.49  unary                                   6
% 7.85/1.49  binary                                  4
% 7.85/1.49  lits                                    63
% 7.85/1.49  lits eq                                 2
% 7.85/1.49  fd_pure                                 0
% 7.85/1.49  fd_pseudo                               0
% 7.85/1.49  fd_cond                                 0
% 7.85/1.49  fd_pseudo_cond                          1
% 7.85/1.49  AC symbols                              0
% 7.85/1.49  
% 7.85/1.49  ------ Schedule dynamic 5 is on 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ 
% 7.85/1.49  Current options:
% 7.85/1.49  ------ 
% 7.85/1.49  
% 7.85/1.49  ------ Input Options
% 7.85/1.49  
% 7.85/1.49  --out_options                           all
% 7.85/1.49  --tptp_safe_out                         true
% 7.85/1.49  --problem_path                          ""
% 7.85/1.49  --include_path                          ""
% 7.85/1.49  --clausifier                            res/vclausify_rel
% 7.85/1.49  --clausifier_options                    ""
% 7.85/1.49  --stdin                                 false
% 7.85/1.49  --stats_out                             all
% 7.85/1.49  
% 7.85/1.49  ------ General Options
% 7.85/1.49  
% 7.85/1.49  --fof                                   false
% 7.85/1.49  --time_out_real                         305.
% 7.85/1.49  --time_out_virtual                      -1.
% 7.85/1.49  --symbol_type_check                     false
% 7.85/1.49  --clausify_out                          false
% 7.85/1.49  --sig_cnt_out                           false
% 7.85/1.49  --trig_cnt_out                          false
% 7.85/1.49  --trig_cnt_out_tolerance                1.
% 7.85/1.49  --trig_cnt_out_sk_spl                   false
% 7.85/1.49  --abstr_cl_out                          false
% 7.85/1.49  
% 7.85/1.49  ------ Global Options
% 7.85/1.49  
% 7.85/1.49  --schedule                              default
% 7.85/1.49  --add_important_lit                     false
% 7.85/1.49  --prop_solver_per_cl                    1000
% 7.85/1.49  --min_unsat_core                        false
% 7.85/1.49  --soft_assumptions                      false
% 7.85/1.49  --soft_lemma_size                       3
% 7.85/1.49  --prop_impl_unit_size                   0
% 7.85/1.49  --prop_impl_unit                        []
% 7.85/1.49  --share_sel_clauses                     true
% 7.85/1.49  --reset_solvers                         false
% 7.85/1.49  --bc_imp_inh                            [conj_cone]
% 7.85/1.49  --conj_cone_tolerance                   3.
% 7.85/1.49  --extra_neg_conj                        none
% 7.85/1.49  --large_theory_mode                     true
% 7.85/1.49  --prolific_symb_bound                   200
% 7.85/1.49  --lt_threshold                          2000
% 7.85/1.49  --clause_weak_htbl                      true
% 7.85/1.49  --gc_record_bc_elim                     false
% 7.85/1.49  
% 7.85/1.49  ------ Preprocessing Options
% 7.85/1.49  
% 7.85/1.49  --preprocessing_flag                    true
% 7.85/1.49  --time_out_prep_mult                    0.1
% 7.85/1.49  --splitting_mode                        input
% 7.85/1.49  --splitting_grd                         true
% 7.85/1.49  --splitting_cvd                         false
% 7.85/1.49  --splitting_cvd_svl                     false
% 7.85/1.49  --splitting_nvd                         32
% 7.85/1.49  --sub_typing                            true
% 7.85/1.49  --prep_gs_sim                           true
% 7.85/1.49  --prep_unflatten                        true
% 7.85/1.49  --prep_res_sim                          true
% 7.85/1.49  --prep_upred                            true
% 7.85/1.49  --prep_sem_filter                       exhaustive
% 7.85/1.49  --prep_sem_filter_out                   false
% 7.85/1.49  --pred_elim                             true
% 7.85/1.49  --res_sim_input                         true
% 7.85/1.49  --eq_ax_congr_red                       true
% 7.85/1.49  --pure_diseq_elim                       true
% 7.85/1.49  --brand_transform                       false
% 7.85/1.49  --non_eq_to_eq                          false
% 7.85/1.49  --prep_def_merge                        true
% 7.85/1.49  --prep_def_merge_prop_impl              false
% 7.85/1.49  --prep_def_merge_mbd                    true
% 7.85/1.49  --prep_def_merge_tr_red                 false
% 7.85/1.49  --prep_def_merge_tr_cl                  false
% 7.85/1.49  --smt_preprocessing                     true
% 7.85/1.49  --smt_ac_axioms                         fast
% 7.85/1.49  --preprocessed_out                      false
% 7.85/1.49  --preprocessed_stats                    false
% 7.85/1.49  
% 7.85/1.49  ------ Abstraction refinement Options
% 7.85/1.49  
% 7.85/1.49  --abstr_ref                             []
% 7.85/1.49  --abstr_ref_prep                        false
% 7.85/1.49  --abstr_ref_until_sat                   false
% 7.85/1.49  --abstr_ref_sig_restrict                funpre
% 7.85/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.85/1.49  --abstr_ref_under                       []
% 7.85/1.49  
% 7.85/1.49  ------ SAT Options
% 7.85/1.49  
% 7.85/1.49  --sat_mode                              false
% 7.85/1.49  --sat_fm_restart_options                ""
% 7.85/1.49  --sat_gr_def                            false
% 7.85/1.49  --sat_epr_types                         true
% 7.85/1.49  --sat_non_cyclic_types                  false
% 7.85/1.49  --sat_finite_models                     false
% 7.85/1.49  --sat_fm_lemmas                         false
% 7.85/1.49  --sat_fm_prep                           false
% 7.85/1.49  --sat_fm_uc_incr                        true
% 7.85/1.49  --sat_out_model                         small
% 7.85/1.49  --sat_out_clauses                       false
% 7.85/1.49  
% 7.85/1.49  ------ QBF Options
% 7.85/1.49  
% 7.85/1.49  --qbf_mode                              false
% 7.85/1.49  --qbf_elim_univ                         false
% 7.85/1.49  --qbf_dom_inst                          none
% 7.85/1.49  --qbf_dom_pre_inst                      false
% 7.85/1.49  --qbf_sk_in                             false
% 7.85/1.49  --qbf_pred_elim                         true
% 7.85/1.49  --qbf_split                             512
% 7.85/1.49  
% 7.85/1.49  ------ BMC1 Options
% 7.85/1.49  
% 7.85/1.49  --bmc1_incremental                      false
% 7.85/1.49  --bmc1_axioms                           reachable_all
% 7.85/1.49  --bmc1_min_bound                        0
% 7.85/1.49  --bmc1_max_bound                        -1
% 7.85/1.49  --bmc1_max_bound_default                -1
% 7.85/1.49  --bmc1_symbol_reachability              true
% 7.85/1.49  --bmc1_property_lemmas                  false
% 7.85/1.49  --bmc1_k_induction                      false
% 7.85/1.49  --bmc1_non_equiv_states                 false
% 7.85/1.49  --bmc1_deadlock                         false
% 7.85/1.49  --bmc1_ucm                              false
% 7.85/1.49  --bmc1_add_unsat_core                   none
% 7.85/1.49  --bmc1_unsat_core_children              false
% 7.85/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.85/1.49  --bmc1_out_stat                         full
% 7.85/1.49  --bmc1_ground_init                      false
% 7.85/1.49  --bmc1_pre_inst_next_state              false
% 7.85/1.49  --bmc1_pre_inst_state                   false
% 7.85/1.49  --bmc1_pre_inst_reach_state             false
% 7.85/1.49  --bmc1_out_unsat_core                   false
% 7.85/1.49  --bmc1_aig_witness_out                  false
% 7.85/1.49  --bmc1_verbose                          false
% 7.85/1.49  --bmc1_dump_clauses_tptp                false
% 7.85/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.85/1.49  --bmc1_dump_file                        -
% 7.85/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.85/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.85/1.49  --bmc1_ucm_extend_mode                  1
% 7.85/1.49  --bmc1_ucm_init_mode                    2
% 7.85/1.49  --bmc1_ucm_cone_mode                    none
% 7.85/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.85/1.49  --bmc1_ucm_relax_model                  4
% 7.85/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.85/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.85/1.49  --bmc1_ucm_layered_model                none
% 7.85/1.49  --bmc1_ucm_max_lemma_size               10
% 7.85/1.49  
% 7.85/1.49  ------ AIG Options
% 7.85/1.49  
% 7.85/1.49  --aig_mode                              false
% 7.85/1.49  
% 7.85/1.49  ------ Instantiation Options
% 7.85/1.49  
% 7.85/1.49  --instantiation_flag                    true
% 7.85/1.49  --inst_sos_flag                         true
% 7.85/1.49  --inst_sos_phase                        true
% 7.85/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.85/1.49  --inst_lit_sel_side                     none
% 7.85/1.49  --inst_solver_per_active                1400
% 7.85/1.49  --inst_solver_calls_frac                1.
% 7.85/1.49  --inst_passive_queue_type               priority_queues
% 7.85/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.85/1.49  --inst_passive_queues_freq              [25;2]
% 7.85/1.49  --inst_dismatching                      true
% 7.85/1.49  --inst_eager_unprocessed_to_passive     true
% 7.85/1.49  --inst_prop_sim_given                   true
% 7.85/1.49  --inst_prop_sim_new                     false
% 7.85/1.49  --inst_subs_new                         false
% 7.85/1.49  --inst_eq_res_simp                      false
% 7.85/1.49  --inst_subs_given                       false
% 7.85/1.49  --inst_orphan_elimination               true
% 7.85/1.49  --inst_learning_loop_flag               true
% 7.85/1.49  --inst_learning_start                   3000
% 7.85/1.49  --inst_learning_factor                  2
% 7.85/1.49  --inst_start_prop_sim_after_learn       3
% 7.85/1.49  --inst_sel_renew                        solver
% 7.85/1.49  --inst_lit_activity_flag                true
% 7.85/1.49  --inst_restr_to_given                   false
% 7.85/1.49  --inst_activity_threshold               500
% 7.85/1.49  --inst_out_proof                        true
% 7.85/1.49  
% 7.85/1.49  ------ Resolution Options
% 7.85/1.49  
% 7.85/1.49  --resolution_flag                       false
% 7.85/1.49  --res_lit_sel                           adaptive
% 7.85/1.49  --res_lit_sel_side                      none
% 7.85/1.49  --res_ordering                          kbo
% 7.85/1.49  --res_to_prop_solver                    active
% 7.85/1.49  --res_prop_simpl_new                    false
% 7.85/1.49  --res_prop_simpl_given                  true
% 7.85/1.49  --res_passive_queue_type                priority_queues
% 7.85/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.85/1.49  --res_passive_queues_freq               [15;5]
% 7.85/1.49  --res_forward_subs                      full
% 7.85/1.49  --res_backward_subs                     full
% 7.85/1.49  --res_forward_subs_resolution           true
% 7.85/1.49  --res_backward_subs_resolution          true
% 7.85/1.49  --res_orphan_elimination                true
% 7.85/1.49  --res_time_limit                        2.
% 7.85/1.49  --res_out_proof                         true
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Options
% 7.85/1.49  
% 7.85/1.49  --superposition_flag                    true
% 7.85/1.49  --sup_passive_queue_type                priority_queues
% 7.85/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.85/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.85/1.49  --demod_completeness_check              fast
% 7.85/1.49  --demod_use_ground                      true
% 7.85/1.49  --sup_to_prop_solver                    passive
% 7.85/1.49  --sup_prop_simpl_new                    true
% 7.85/1.49  --sup_prop_simpl_given                  true
% 7.85/1.49  --sup_fun_splitting                     true
% 7.85/1.49  --sup_smt_interval                      50000
% 7.85/1.49  
% 7.85/1.49  ------ Superposition Simplification Setup
% 7.85/1.49  
% 7.85/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.85/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.85/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.85/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.85/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_immed_triv                        [TrivRules]
% 7.85/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_immed_bw_main                     []
% 7.85/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.85/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.85/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.85/1.49  --sup_input_bw                          []
% 7.85/1.49  
% 7.85/1.49  ------ Combination Options
% 7.85/1.49  
% 7.85/1.49  --comb_res_mult                         3
% 7.85/1.49  --comb_sup_mult                         2
% 7.85/1.49  --comb_inst_mult                        10
% 7.85/1.49  
% 7.85/1.49  ------ Debug Options
% 7.85/1.49  
% 7.85/1.49  --dbg_backtrace                         false
% 7.85/1.49  --dbg_dump_prop_clauses                 false
% 7.85/1.49  --dbg_dump_prop_clauses_file            -
% 7.85/1.49  --dbg_out_stat                          false
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  ------ Proving...
% 7.85/1.49  
% 7.85/1.49  
% 7.85/1.49  % SZS status Theorem for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.49  
% 7.85/1.49  fof(f3,axiom,(
% 7.85/1.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f16,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.85/1.49    inference(ennf_transformation,[],[f3])).
% 7.85/1.49  
% 7.85/1.49  fof(f17,plain,(
% 7.85/1.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.85/1.49    inference(flattening,[],[f16])).
% 7.85/1.49  
% 7.85/1.49  fof(f49,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f17])).
% 7.85/1.49  
% 7.85/1.49  fof(f13,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f28,plain,(
% 7.85/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f13])).
% 7.85/1.49  
% 7.85/1.49  fof(f29,plain,(
% 7.85/1.49    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(flattening,[],[f28])).
% 7.85/1.49  
% 7.85/1.49  fof(f37,plain,(
% 7.85/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(nnf_transformation,[],[f29])).
% 7.85/1.49  
% 7.85/1.49  fof(f38,plain,(
% 7.85/1.49    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(rectify,[],[f37])).
% 7.85/1.49  
% 7.85/1.49  fof(f39,plain,(
% 7.85/1.49    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f40,plain,(
% 7.85/1.49    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f38,f39])).
% 7.85/1.49  
% 7.85/1.49  fof(f61,plain,(
% 7.85/1.49    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f40])).
% 7.85/1.49  
% 7.85/1.49  fof(f10,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f24,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f10])).
% 7.85/1.49  
% 7.85/1.49  fof(f25,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(flattening,[],[f24])).
% 7.85/1.49  
% 7.85/1.49  fof(f58,plain,(
% 7.85/1.49    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f25])).
% 7.85/1.49  
% 7.85/1.49  fof(f72,plain,(
% 7.85/1.49    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(equality_resolution,[],[f58])).
% 7.85/1.49  
% 7.85/1.49  fof(f7,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f21,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f7])).
% 7.85/1.49  
% 7.85/1.49  fof(f54,plain,(
% 7.85/1.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f21])).
% 7.85/1.49  
% 7.85/1.49  fof(f12,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f27,plain,(
% 7.85/1.49    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f12])).
% 7.85/1.49  
% 7.85/1.49  fof(f60,plain,(
% 7.85/1.49    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f27])).
% 7.85/1.49  
% 7.85/1.49  fof(f14,conjecture,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f15,negated_conjecture,(
% 7.85/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.85/1.49    inference(negated_conjecture,[],[f14])).
% 7.85/1.49  
% 7.85/1.49  fof(f30,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f15])).
% 7.85/1.49  
% 7.85/1.49  fof(f31,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.85/1.49    inference(flattening,[],[f30])).
% 7.85/1.49  
% 7.85/1.49  fof(f42,plain,(
% 7.85/1.49    ( ! [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK2) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK2))) )),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f41,plain,(
% 7.85/1.49    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 7.85/1.49    introduced(choice_axiom,[])).
% 7.85/1.49  
% 7.85/1.49  fof(f43,plain,(
% 7.85/1.49    (~v3_tdlat_3(sK2) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 7.85/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f31,f42,f41])).
% 7.85/1.49  
% 7.85/1.49  fof(f67,plain,(
% 7.85/1.49    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.85/1.49    inference(cnf_transformation,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  fof(f9,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f23,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f9])).
% 7.85/1.49  
% 7.85/1.49  fof(f36,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(nnf_transformation,[],[f23])).
% 7.85/1.49  
% 7.85/1.49  fof(f56,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f36])).
% 7.85/1.49  
% 7.85/1.49  fof(f5,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f19,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f5])).
% 7.85/1.49  
% 7.85/1.49  fof(f52,plain,(
% 7.85/1.49    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f19])).
% 7.85/1.49  
% 7.85/1.49  fof(f65,plain,(
% 7.85/1.49    l1_pre_topc(sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  fof(f8,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f22,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f8])).
% 7.85/1.49  
% 7.85/1.49  fof(f55,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f22])).
% 7.85/1.49  
% 7.85/1.49  fof(f66,plain,(
% 7.85/1.49    l1_pre_topc(sK2)),
% 7.85/1.49    inference(cnf_transformation,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  fof(f62,plain,(
% 7.85/1.49    ( ! [X0] : (v3_tdlat_3(X0) | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f40])).
% 7.85/1.49  
% 7.85/1.49  fof(f11,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f26,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f11])).
% 7.85/1.49  
% 7.85/1.49  fof(f59,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f26])).
% 7.85/1.49  
% 7.85/1.49  fof(f2,axiom,(
% 7.85/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f34,plain,(
% 7.85/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.85/1.49    inference(nnf_transformation,[],[f2])).
% 7.85/1.49  
% 7.85/1.49  fof(f47,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.85/1.49    inference(cnf_transformation,[],[f34])).
% 7.85/1.49  
% 7.85/1.49  fof(f1,axiom,(
% 7.85/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f32,plain,(
% 7.85/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.49    inference(nnf_transformation,[],[f1])).
% 7.85/1.49  
% 7.85/1.49  fof(f33,plain,(
% 7.85/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.49    inference(flattening,[],[f32])).
% 7.85/1.49  
% 7.85/1.49  fof(f46,plain,(
% 7.85/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f69,plain,(
% 7.85/1.49    ~v3_tdlat_3(sK2)),
% 7.85/1.49    inference(cnf_transformation,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  fof(f4,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f18,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f4])).
% 7.85/1.49  
% 7.85/1.49  fof(f35,plain,(
% 7.85/1.49    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(nnf_transformation,[],[f18])).
% 7.85/1.49  
% 7.85/1.49  fof(f50,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f35])).
% 7.85/1.49  
% 7.85/1.49  fof(f48,plain,(
% 7.85/1.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f34])).
% 7.85/1.49  
% 7.85/1.49  fof(f51,plain,(
% 7.85/1.49    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f35])).
% 7.85/1.49  
% 7.85/1.49  fof(f44,plain,(
% 7.85/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.85/1.49    inference(cnf_transformation,[],[f33])).
% 7.85/1.49  
% 7.85/1.49  fof(f71,plain,(
% 7.85/1.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.85/1.49    inference(equality_resolution,[],[f44])).
% 7.85/1.49  
% 7.85/1.49  fof(f64,plain,(
% 7.85/1.49    ( ! [X0] : (v3_tdlat_3(X0) | ~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f40])).
% 7.85/1.49  
% 7.85/1.49  fof(f63,plain,(
% 7.85/1.49    ( ! [X0] : (v3_tdlat_3(X0) | r2_hidden(sK0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f40])).
% 7.85/1.49  
% 7.85/1.49  fof(f6,axiom,(
% 7.85/1.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.85/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.49  
% 7.85/1.49  fof(f20,plain,(
% 7.85/1.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.85/1.49    inference(ennf_transformation,[],[f6])).
% 7.85/1.49  
% 7.85/1.49  fof(f53,plain,(
% 7.85/1.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.85/1.49    inference(cnf_transformation,[],[f20])).
% 7.85/1.49  
% 7.85/1.49  fof(f68,plain,(
% 7.85/1.49    v3_tdlat_3(sK1)),
% 7.85/1.49    inference(cnf_transformation,[],[f43])).
% 7.85/1.49  
% 7.85/1.49  cnf(c_799,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.85/1.49      theory(equality) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2499,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,X1)
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
% 7.85/1.49      | X2 != X1
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0 ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_799]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2892,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(X0,X1),X2)
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X3)
% 7.85/1.49      | X3 != X2
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2499]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_6515,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(X0,sK0(sK2)),X1)
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
% 7.85/1.49      | X2 != X1
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,sK0(sK2)) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2892]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9737,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
% 7.85/1.49      | X2 != X1
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_6515]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16918,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X1)
% 7.85/1.49      | X1 != u1_pre_topc(X0)
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_9737]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_23043,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.85/1.49      | u1_pre_topc(X0) != u1_pre_topc(X0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_16918]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_23045,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
% 7.85/1.49      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.85/1.49      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_23043]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,X1)
% 7.85/1.49      | m1_subset_1(X0,X2)
% 7.85/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2789,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,X1)
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.49      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3961,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.49      | ~ m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_2789]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_5703,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
% 7.85/1.49      | m1_subset_1(k6_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_3961]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16905,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.49      | m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_5703]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16907,plain,
% 7.85/1.49      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.85/1.49      | m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.49      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_16905]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_20,plain,
% 7.85/1.49      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.85/1.49      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 7.85/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ v3_tdlat_3(X1)
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12665,plain,
% 7.85/1.49      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 7.85/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | ~ v3_tdlat_3(X0)
% 7.85/1.49      | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_20]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12682,plain,
% 7.85/1.49      ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.85/1.49      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 7.85/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.49      | ~ v3_tdlat_3(sK1)
% 7.85/1.49      | ~ l1_pre_topc(sK1) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_12665]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_14,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ v3_pre_topc(X2,X1)
% 7.85/1.49      | v3_pre_topc(X2,X0)
% 7.85/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_10,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_136,plain,
% 7.85/1.49      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | v3_pre_topc(X2,X0)
% 7.85/1.49      | ~ v3_pre_topc(X2,X1)
% 7.85/1.49      | ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_14,c_10]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_137,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ v3_pre_topc(X2,X1)
% 7.85/1.49      | v3_pre_topc(X2,X0)
% 7.85/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_136]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12489,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,sK2)
% 7.85/1.49      | v3_pre_topc(sK0(sK2),X0)
% 7.85/1.49      | ~ v3_pre_topc(sK0(sK2),sK2)
% 7.85/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | ~ l1_pre_topc(sK2) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_137]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_12491,plain,
% 7.85/1.49      ( ~ m1_pre_topc(sK1,sK2)
% 7.85/1.49      | v3_pre_topc(sK0(sK2),sK1)
% 7.85/1.49      | ~ v3_pre_topc(sK0(sK2),sK2)
% 7.85/1.49      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.49      | ~ l1_pre_topc(sK2) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_12489]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_16,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1333,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_23,negated_conjecture,
% 7.85/1.49      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.85/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_13,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X0)
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f56]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_141,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.85/1.49      | ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_13,c_8]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_142,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_141]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1323,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_142]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1715,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_23,c_1323]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_25,negated_conjecture,
% 7.85/1.49      ( l1_pre_topc(sK1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_26,plain,
% 7.85/1.49      ( l1_pre_topc(sK1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1894,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_1715,c_26]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1895,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_1894]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_11,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1)
% 7.85/1.49      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f55]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1335,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2300,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1895,c_1335]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_24,negated_conjecture,
% 7.85/1.49      ( l1_pre_topc(sK2) ),
% 7.85/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_27,plain,
% 7.85/1.49      ( l1_pre_topc(sK2) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2422,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK2) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) != iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2300,c_27]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2423,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) = iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_2422]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2428,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1333,c_2423]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_36,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X0) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_38,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,sK1) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_36]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1612,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.85/1.49      | m1_pre_topc(X0,sK2)
% 7.85/1.49      | ~ l1_pre_topc(sK2) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_11]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1613,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_1612]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1615,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1613]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1717,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_1715]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2559,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2428,c_26,c_27,c_38,c_1615,c_1717]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_19,plain,
% 7.85/1.49      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | v3_tdlat_3(X0)
% 7.85/1.49      | ~ l1_pre_topc(X0) ),
% 7.85/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1330,plain,
% 7.85/1.49      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.85/1.49      | v3_tdlat_3(X0) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2301,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_23,c_1335]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2408,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2301,c_26]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2409,plain,
% 7.85/1.49      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_2408]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2414,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1323,c_2409]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2481,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2414,c_27]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2482,plain,
% 7.85/1.49      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.85/1.49      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_2481]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2487,plain,
% 7.85/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1333,c_2482]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2628,plain,
% 7.85/1.49      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_2487,c_27]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_15,plain,
% 7.85/1.49      ( ~ m1_pre_topc(X0,X1)
% 7.85/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f59]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1334,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1342,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.85/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2125,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1334,c_1342]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_0,plain,
% 7.85/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.85/1.49      inference(cnf_transformation,[],[f46]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1345,plain,
% 7.85/1.49      ( X0 = X1
% 7.85/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.85/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3001,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2125,c_1345]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3504,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2125,c_3001]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_52,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4062,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_3504,c_52]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4063,plain,
% 7.85/1.49      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(X1,X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_4062]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4069,plain,
% 7.85/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 7.85/1.49      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2628,c_4063]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4592,plain,
% 7.85/1.49      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_4069,c_26,c_27,c_38,c_1615,c_1717]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1336,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.85/1.49      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4616,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.85/1.49      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_4592,c_1336]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7516,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.85/1.49      | v3_tdlat_3(sK2) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1330,c_4616]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_21,negated_conjecture,
% 7.85/1.49      ( ~ v3_tdlat_3(sK2) ),
% 7.85/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_29,plain,
% 7.85/1.49      ( v3_tdlat_3(sK2) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8056,plain,
% 7.85/1.49      ( l1_pre_topc(X0) != iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_7516,c_27,c_29]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8057,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_8056]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_8066,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | l1_pre_topc(X0) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_8057,c_1336]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9519,plain,
% 7.85/1.49      ( l1_pre_topc(X1) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_pre_topc(X0,X1) != iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_8066,c_52]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9520,plain,
% 7.85/1.49      ( m1_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | m1_pre_topc(sK1,X0) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(renaming,[status(thm)],[c_9519]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_9527,plain,
% 7.85/1.49      ( m1_pre_topc(sK1,sK1) != iProver_top
% 7.85/1.49      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_2559,c_9520]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_380,plain,
% 7.85/1.49      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.49      | ~ l1_pre_topc(X0)
% 7.85/1.49      | sK2 != X0 ),
% 7.85/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_381,plain,
% 7.85/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.49      | ~ l1_pre_topc(sK2) ),
% 7.85/1.49      inference(unflattening,[status(thm)],[c_380]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_382,plain,
% 7.85/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.85/1.49      | l1_pre_topc(sK2) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_11050,plain,
% 7.85/1.49      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.85/1.49      inference(global_propositional_subsumption,
% 7.85/1.49                [status(thm)],
% 7.85/1.49                [c_9527,c_27,c_382]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_7,plain,
% 7.85/1.49      ( ~ v3_pre_topc(X0,X1)
% 7.85/1.49      | r2_hidden(X0,u1_pre_topc(X1))
% 7.85/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.49      | ~ l1_pre_topc(X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1339,plain,
% 7.85/1.49      ( v3_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4632,plain,
% 7.85/1.49      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.85/1.49      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.85/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.85/1.49      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_4592,c_1339]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2577,plain,
% 7.85/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.49      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 7.85/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2578,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.85/1.49      | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_2577]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_3,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.85/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_1343,plain,
% 7.85/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.85/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.85/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_2753,plain,
% 7.85/1.49      ( v3_pre_topc(X0,X1) != iProver_top
% 7.85/1.49      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 7.85/1.49      | r1_tarski(X0,u1_struct_0(X1)) != iProver_top
% 7.85/1.49      | l1_pre_topc(X1) != iProver_top ),
% 7.85/1.49      inference(superposition,[status(thm)],[c_1343,c_1339]) ).
% 7.85/1.49  
% 7.85/1.49  cnf(c_4629,plain,
% 7.85/1.49      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.85/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.85/1.50      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 7.85/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_4592,c_2753]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6022,plain,
% 7.85/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.85/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.85/1.50      | v3_pre_topc(X0,sK1) != iProver_top ),
% 7.85/1.50      inference(global_propositional_subsumption,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_4632,c_26,c_2578,c_4629]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6023,plain,
% 7.85/1.50      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.85/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.85/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.85/1.50      inference(renaming,[status(thm)],[c_6022]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11059,plain,
% 7.85/1.50      ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
% 7.85/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top ),
% 7.85/1.50      inference(superposition,[status(thm)],[c_11050,c_6023]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_11072,plain,
% 7.85/1.50      ( ~ v3_pre_topc(sK0(sK2),sK1)
% 7.85/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) ),
% 7.85/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_11059]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_798,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2198,plain,
% 7.85/1.50      ( ~ m1_subset_1(X0,X1)
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X2)) != X1 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_798]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2519,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),X2)
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X3)) != X2 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2198]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2907,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2519]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6514,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(X0,sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,sK0(sK2))
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2907]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9727,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_6514]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9729,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_9727]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2913,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X2))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(X3)) != k1_zfmisc_1(X2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2519]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_4757,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2913]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9671,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_4757]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9675,plain,
% 7.85/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_9671]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_806,plain,
% 7.85/1.50      ( X0 != X1 | X2 != X3 | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3812,plain,
% 7.85/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
% 7.85/1.50      | sK0(sK2) != X1
% 7.85/1.50      | u1_struct_0(sK2) != X0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_806]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_5360,plain,
% 7.85/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
% 7.85/1.50      | sK0(sK2) != sK0(sK2)
% 7.85/1.50      | u1_struct_0(sK2) != X0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3812]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7136,plain,
% 7.85/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.85/1.50      | sK0(sK2) != sK0(sK2)
% 7.85/1.50      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_5360]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_7137,plain,
% 7.85/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.85/1.50      | sK0(sK2) != sK0(sK2)
% 7.85/1.50      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_7136]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_795,plain,( X0 = X0 ),theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3915,plain,
% 7.85/1.50      ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_795]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3916,plain,
% 7.85/1.50      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3915]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_6,plain,
% 7.85/1.50      ( v3_pre_topc(X0,X1)
% 7.85/1.50      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.85/1.50      | ~ l1_pre_topc(X1) ),
% 7.85/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3755,plain,
% 7.85/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
% 7.85/1.50      | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
% 7.85/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3757,plain,
% 7.85/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
% 7.85/1.50      | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
% 7.85/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3755]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3531,plain,
% 7.85/1.50      ( ~ m1_pre_topc(sK2,X0)
% 7.85/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.85/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_10]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_3533,plain,
% 7.85/1.50      ( ~ m1_pre_topc(sK2,sK1)
% 7.85/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.85/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_3531]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_797,plain,
% 7.85/1.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2025,plain,
% 7.85/1.50      ( u1_struct_0(sK2) != X0
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_797]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2556,plain,
% 7.85/1.50      ( u1_struct_0(sK2) != u1_struct_0(X0)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2025]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2557,plain,
% 7.85/1.50      ( u1_struct_0(sK2) != u1_struct_0(sK1)
% 7.85/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2556]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2488,plain,
% 7.85/1.50      ( m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2487]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_2,plain,
% 7.85/1.50      ( r1_tarski(X0,X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1978,plain,
% 7.85/1.50      ( r1_tarski(sK0(sK2),sK0(sK2)) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1676,plain,
% 7.85/1.50      ( v3_pre_topc(X0,sK2)
% 7.85/1.50      | ~ r2_hidden(X0,u1_pre_topc(sK2))
% 7.85/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_6]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1917,plain,
% 7.85/1.50      ( v3_pre_topc(sK0(sK2),sK2)
% 7.85/1.50      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.85/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1676]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1636,plain,
% 7.85/1.50      ( ~ r1_tarski(X0,sK0(sK2))
% 7.85/1.50      | ~ r1_tarski(sK0(sK2),X0)
% 7.85/1.50      | sK0(sK2) = X0 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1883,plain,
% 7.85/1.50      ( ~ r1_tarski(sK0(sK2),sK0(sK2)) | sK0(sK2) = sK0(sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1636]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1716,plain,
% 7.85/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.85/1.50      | ~ m1_pre_topc(X0,sK1)
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1715]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1718,plain,
% 7.85/1.50      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.85/1.50      | ~ m1_pre_topc(sK1,sK1)
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1716]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1614,plain,
% 7.85/1.50      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.85/1.50      | m1_pre_topc(sK1,sK2)
% 7.85/1.50      | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1612]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1410,plain,
% 7.85/1.50      ( ~ m1_pre_topc(sK2,X0)
% 7.85/1.50      | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
% 7.85/1.50      | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.85/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_137]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1412,plain,
% 7.85/1.50      ( ~ m1_pre_topc(sK2,sK1)
% 7.85/1.50      | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
% 7.85/1.50      | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.85/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_1410]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_1387,plain,
% 7.85/1.50      ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.85/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 7.85/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.85/1.50      | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_800,plain,
% 7.85/1.50      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.85/1.50      theory(equality) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_810,plain,
% 7.85/1.50      ( u1_pre_topc(sK1) = u1_pre_topc(sK1) | sK1 != sK1 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_800]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_17,plain,
% 7.85/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 7.85/1.50      | v3_tdlat_3(X0)
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_402,plain,
% 7.85/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 7.85/1.50      | ~ l1_pre_topc(X0)
% 7.85/1.50      | sK2 != X0 ),
% 7.85/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_21]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_403,plain,
% 7.85/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK2))
% 7.85/1.50      | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(unflattening,[status(thm)],[c_402]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_18,plain,
% 7.85/1.50      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 7.85/1.50      | v3_tdlat_3(X0)
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_391,plain,
% 7.85/1.50      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 7.85/1.50      | ~ l1_pre_topc(X0)
% 7.85/1.50      | sK2 != X0 ),
% 7.85/1.50      inference(resolution_lifted,[status(thm)],[c_18,c_21]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_392,plain,
% 7.85/1.50      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) | ~ l1_pre_topc(sK2) ),
% 7.85/1.50      inference(unflattening,[status(thm)],[c_391]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_73,plain,
% 7.85/1.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_69,plain,
% 7.85/1.50      ( r1_tarski(sK1,sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_9,plain,
% 7.85/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.85/1.50      | ~ l1_pre_topc(X0) ),
% 7.85/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_50,plain,
% 7.85/1.50      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.85/1.50      | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_37,plain,
% 7.85/1.50      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 7.85/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(c_22,negated_conjecture,
% 7.85/1.50      ( v3_tdlat_3(sK1) ),
% 7.85/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.85/1.50  
% 7.85/1.50  cnf(contradiction,plain,
% 7.85/1.50      ( $false ),
% 7.85/1.50      inference(minisat,
% 7.85/1.50                [status(thm)],
% 7.85/1.50                [c_23045,c_16907,c_12682,c_12491,c_11072,c_9729,c_9675,
% 7.85/1.50                 c_7137,c_4069,c_3916,c_3757,c_3533,c_2557,c_2488,c_1978,
% 7.85/1.50                 c_1917,c_1883,c_1718,c_1717,c_1615,c_1614,c_1412,c_1387,
% 7.85/1.50                 c_810,c_403,c_392,c_381,c_73,c_69,c_50,c_38,c_37,c_22,
% 7.85/1.50                 c_27,c_24,c_26,c_25]) ).
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.50  
% 7.85/1.50  ------                               Statistics
% 7.85/1.50  
% 7.85/1.50  ------ General
% 7.85/1.50  
% 7.85/1.50  abstr_ref_over_cycles:                  0
% 7.85/1.50  abstr_ref_under_cycles:                 0
% 7.85/1.50  gc_basic_clause_elim:                   0
% 7.85/1.50  forced_gc_time:                         0
% 7.85/1.50  parsing_time:                           0.008
% 7.85/1.50  unif_index_cands_time:                  0.
% 7.85/1.50  unif_index_add_time:                    0.
% 7.85/1.50  orderings_time:                         0.
% 7.85/1.50  out_proof_time:                         0.014
% 7.85/1.50  total_time:                             0.73
% 7.85/1.50  num_of_symbols:                         46
% 7.85/1.50  num_of_terms:                           11351
% 7.85/1.50  
% 7.85/1.50  ------ Preprocessing
% 7.85/1.50  
% 7.85/1.50  num_of_splits:                          0
% 7.85/1.50  num_of_split_atoms:                     0
% 7.85/1.50  num_of_reused_defs:                     0
% 7.85/1.50  num_eq_ax_congr_red:                    18
% 7.85/1.50  num_of_sem_filtered_clauses:            1
% 7.85/1.50  num_of_subtypes:                        0
% 7.85/1.50  monotx_restored_types:                  0
% 7.85/1.50  sat_num_of_epr_types:                   0
% 7.85/1.50  sat_num_of_non_cyclic_types:            0
% 7.85/1.50  sat_guarded_non_collapsed_types:        0
% 7.85/1.50  num_pure_diseq_elim:                    0
% 7.85/1.50  simp_replaced_by:                       0
% 7.85/1.50  res_preprocessed:                       121
% 7.85/1.50  prep_upred:                             0
% 7.85/1.50  prep_unflattend:                        14
% 7.85/1.50  smt_new_axioms:                         0
% 7.85/1.50  pred_elim_cands:                        7
% 7.85/1.50  pred_elim:                              0
% 7.85/1.50  pred_elim_cl:                           0
% 7.85/1.50  pred_elim_cycles:                       2
% 7.85/1.50  merged_defs:                            8
% 7.85/1.50  merged_defs_ncl:                        0
% 7.85/1.50  bin_hyper_res:                          8
% 7.85/1.50  prep_cycles:                            4
% 7.85/1.50  pred_elim_time:                         0.005
% 7.85/1.50  splitting_time:                         0.
% 7.85/1.50  sem_filter_time:                        0.
% 7.85/1.50  monotx_time:                            0.001
% 7.85/1.50  subtype_inf_time:                       0.
% 7.85/1.50  
% 7.85/1.50  ------ Problem properties
% 7.85/1.50  
% 7.85/1.50  clauses:                                24
% 7.85/1.50  conjectures:                            5
% 7.85/1.50  epr:                                    8
% 7.85/1.50  horn:                                   22
% 7.85/1.50  ground:                                 5
% 7.85/1.50  unary:                                  6
% 7.85/1.50  binary:                                 4
% 7.85/1.50  lits:                                   63
% 7.85/1.50  lits_eq:                                2
% 7.85/1.50  fd_pure:                                0
% 7.85/1.50  fd_pseudo:                              0
% 7.85/1.50  fd_cond:                                0
% 7.85/1.50  fd_pseudo_cond:                         1
% 7.85/1.50  ac_symbols:                             0
% 7.85/1.50  
% 7.85/1.50  ------ Propositional Solver
% 7.85/1.50  
% 7.85/1.50  prop_solver_calls:                      39
% 7.85/1.50  prop_fast_solver_calls:                 2825
% 7.85/1.50  smt_solver_calls:                       0
% 7.85/1.50  smt_fast_solver_calls:                  0
% 7.85/1.50  prop_num_of_clauses:                    8134
% 7.85/1.50  prop_preprocess_simplified:             12238
% 7.85/1.50  prop_fo_subsumed:                       202
% 7.85/1.50  prop_solver_time:                       0.
% 7.85/1.50  smt_solver_time:                        0.
% 7.85/1.50  smt_fast_solver_time:                   0.
% 7.85/1.50  prop_fast_solver_time:                  0.
% 7.85/1.50  prop_unsat_core_time:                   0.
% 7.85/1.50  
% 7.85/1.50  ------ QBF
% 7.85/1.50  
% 7.85/1.50  qbf_q_res:                              0
% 7.85/1.50  qbf_num_tautologies:                    0
% 7.85/1.50  qbf_prep_cycles:                        0
% 7.85/1.50  
% 7.85/1.50  ------ BMC1
% 7.85/1.50  
% 7.85/1.50  bmc1_current_bound:                     -1
% 7.85/1.50  bmc1_last_solved_bound:                 -1
% 7.85/1.50  bmc1_unsat_core_size:                   -1
% 7.85/1.50  bmc1_unsat_core_parents_size:           -1
% 7.85/1.50  bmc1_merge_next_fun:                    0
% 7.85/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.85/1.50  
% 7.85/1.50  ------ Instantiation
% 7.85/1.50  
% 7.85/1.50  inst_num_of_clauses:                    1827
% 7.85/1.50  inst_num_in_passive:                    200
% 7.85/1.50  inst_num_in_active:                     1552
% 7.85/1.50  inst_num_in_unprocessed:                74
% 7.85/1.50  inst_num_of_loops:                      1665
% 7.85/1.50  inst_num_of_learning_restarts:          0
% 7.85/1.50  inst_num_moves_active_passive:          101
% 7.85/1.50  inst_lit_activity:                      0
% 7.85/1.50  inst_lit_activity_moves:                0
% 7.85/1.50  inst_num_tautologies:                   0
% 7.85/1.50  inst_num_prop_implied:                  0
% 7.85/1.50  inst_num_existing_simplified:           0
% 7.85/1.50  inst_num_eq_res_simplified:             0
% 7.85/1.50  inst_num_child_elim:                    0
% 7.85/1.50  inst_num_of_dismatching_blockings:      2836
% 7.85/1.50  inst_num_of_non_proper_insts:           5449
% 7.85/1.50  inst_num_of_duplicates:                 0
% 7.85/1.50  inst_inst_num_from_inst_to_res:         0
% 7.85/1.50  inst_dismatching_checking_time:         0.
% 7.85/1.50  
% 7.85/1.50  ------ Resolution
% 7.85/1.50  
% 7.85/1.50  res_num_of_clauses:                     0
% 7.85/1.50  res_num_in_passive:                     0
% 7.85/1.50  res_num_in_active:                      0
% 7.85/1.50  res_num_of_loops:                       125
% 7.85/1.50  res_forward_subset_subsumed:            1065
% 7.85/1.50  res_backward_subset_subsumed:           0
% 7.85/1.50  res_forward_subsumed:                   0
% 7.85/1.50  res_backward_subsumed:                  0
% 7.85/1.50  res_forward_subsumption_resolution:     0
% 7.85/1.50  res_backward_subsumption_resolution:    0
% 7.85/1.50  res_clause_to_clause_subsumption:       4719
% 7.85/1.50  res_orphan_elimination:                 0
% 7.85/1.50  res_tautology_del:                      942
% 7.85/1.50  res_num_eq_res_simplified:              0
% 7.85/1.50  res_num_sel_changes:                    0
% 7.85/1.50  res_moves_from_active_to_pass:          0
% 7.85/1.50  
% 7.85/1.50  ------ Superposition
% 7.85/1.50  
% 7.85/1.50  sup_time_total:                         0.
% 7.85/1.50  sup_time_generating:                    0.
% 7.85/1.50  sup_time_sim_full:                      0.
% 7.85/1.50  sup_time_sim_immed:                     0.
% 7.85/1.50  
% 7.85/1.50  sup_num_of_clauses:                     850
% 7.85/1.50  sup_num_in_active:                      324
% 7.85/1.50  sup_num_in_passive:                     526
% 7.85/1.50  sup_num_of_loops:                       332
% 7.85/1.50  sup_fw_superposition:                   834
% 7.85/1.50  sup_bw_superposition:                   906
% 7.85/1.50  sup_immediate_simplified:               558
% 7.85/1.50  sup_given_eliminated:                   0
% 7.85/1.50  comparisons_done:                       0
% 7.85/1.50  comparisons_avoided:                    0
% 7.85/1.50  
% 7.85/1.50  ------ Simplifications
% 7.85/1.50  
% 7.85/1.50  
% 7.85/1.50  sim_fw_subset_subsumed:                 147
% 7.85/1.50  sim_bw_subset_subsumed:                 30
% 7.85/1.50  sim_fw_subsumed:                        336
% 7.85/1.50  sim_bw_subsumed:                        13
% 7.85/1.50  sim_fw_subsumption_res:                 0
% 7.85/1.50  sim_bw_subsumption_res:                 0
% 7.85/1.50  sim_tautology_del:                      54
% 7.85/1.50  sim_eq_tautology_del:                   28
% 7.85/1.50  sim_eq_res_simp:                        0
% 7.85/1.50  sim_fw_demodulated:                     6
% 7.85/1.50  sim_bw_demodulated:                     3
% 7.85/1.50  sim_light_normalised:                   133
% 7.85/1.50  sim_joinable_taut:                      0
% 7.85/1.50  sim_joinable_simp:                      0
% 7.85/1.50  sim_ac_normalised:                      0
% 7.85/1.50  sim_smt_subsumption:                    0
% 7.85/1.50  
%------------------------------------------------------------------------------
