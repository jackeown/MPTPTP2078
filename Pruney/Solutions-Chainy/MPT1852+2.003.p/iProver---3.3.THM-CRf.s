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
% DateTime   : Thu Dec  3 12:25:33 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  227 (2019 expanded)
%              Number of clauses        :  162 ( 747 expanded)
%              Number of leaves         :   22 ( 439 expanded)
%              Depth                    :   27
%              Number of atoms          :  756 (8079 expanded)
%              Number of equality atoms :  301 (1977 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r2_hidden(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
        & r2_hidden(sK0(X0),u1_pre_topc(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f57,plain,(
    ! [X2,X0] :
      ( r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r2_hidden(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
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

fof(f39,plain,
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

fof(f41,plain,
    ( ~ v3_tdlat_3(sK2)
    & v3_tdlat_3(sK1)
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f40,f39])).

fof(f63,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f68,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f59,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | r2_hidden(sK0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,(
    v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0] :
      ( v3_tdlat_3(X0)
      | ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

cnf(c_672,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1821,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
    | X2 != X1
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_2252,plain,
    ( ~ r2_hidden(k6_subset_1(X0,X1),X2)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X3)
    | X3 != X2
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_1821])).

cnf(c_3883,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
    | X2 != X1
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_13672,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X1)
    | X1 != u1_pre_topc(X0)
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3883])).

cnf(c_21466,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X1))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | u1_pre_topc(X1) != u1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_13672])).

cnf(c_21468,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_21466])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1878,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2486,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_1878])).

cnf(c_3164,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
    | m1_subset_1(k6_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
    inference(instantiation,[status(thm)],[c_2486])).

cnf(c_13658,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
    inference(instantiation,[status(thm)],[c_3164])).

cnf(c_13660,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_13658])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,u1_pre_topc(X1))
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_tdlat_3(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9122,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_9137,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v3_tdlat_3(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_9122])).

cnf(c_13,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1057,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_129,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_6])).

cnf(c_130,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_1046,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_130])).

cnf(c_21,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1058,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1807,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1058])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1911,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_24])).

cnf(c_1912,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1911])).

cnf(c_1917,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1912])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2169,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1917,c_25])).

cnf(c_2170,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2169])).

cnf(c_2175,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_2170])).

cnf(c_2357,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2175,c_25])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1056,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1066,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1631,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1066])).

cnf(c_2574,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1056,c_1631])).

cnf(c_50,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2805,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(X1)
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2574,c_50])).

cnf(c_2806,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2805])).

cnf(c_2812,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK1,sK2) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2357,c_2806])).

cnf(c_37,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_39,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1251,plain,
    ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(X0,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1252,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1251])).

cnf(c_1254,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_1428,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1046])).

cnf(c_1430,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1428])).

cnf(c_3304,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2812,c_24,c_25,c_39,c_1254,c_1430])).

cnf(c_17,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1053,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v3_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1059,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3313,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_1059])).

cnf(c_4394,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | v3_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_3313])).

cnf(c_19,negated_conjecture,
    ( ~ v3_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,plain,
    ( v3_tdlat_3(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4698,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4394,c_25,c_27])).

cnf(c_4699,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4698])).

cnf(c_4704,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_4699])).

cnf(c_311,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_19])).

cnf(c_312,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_313,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_312])).

cnf(c_4831,plain,
    ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4704,c_25,c_313])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_124,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | v3_pre_topc(X2,X0)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_8])).

cnf(c_125,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_124])).

cnf(c_1047,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | v3_pre_topc(X2,X1) != iProver_top
    | v3_pre_topc(X2,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_125])).

cnf(c_4838,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | v3_pre_topc(sK0(sK2),X0) != iProver_top
    | v3_pre_topc(sK0(sK2),sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4831,c_1047])).

cnf(c_16,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_322,plain,
    ( r2_hidden(sK0(X0),u1_pre_topc(X0))
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_323,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_324,plain,
    ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_4,plain,
    ( v3_pre_topc(X0,X1)
    | ~ r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1859,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ r2_hidden(X0,u1_pre_topc(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2384,plain,
    ( v3_pre_topc(sK0(sK2),sK2)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_2385,plain,
    ( v3_pre_topc(sK0(sK2),sK2) = iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK2)) != iProver_top
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2384])).

cnf(c_5671,plain,
    ( v3_pre_topc(sK0(sK2),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4838,c_25,c_313,c_324,c_2385])).

cnf(c_3314,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(X1,X0) != iProver_top
    | v3_pre_topc(X1,sK1) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_1047])).

cnf(c_4840,plain,
    ( m1_pre_topc(sK1,X0) != iProver_top
    | v3_pre_topc(sK0(sK2),X0) != iProver_top
    | v3_pre_topc(sK0(sK2),sK1) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4831,c_3314])).

cnf(c_5777,plain,
    ( m1_pre_topc(sK1,sK2) != iProver_top
    | v3_pre_topc(sK0(sK2),sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5671,c_4840])).

cnf(c_5778,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | v3_pre_topc(sK0(sK2),sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5777])).

cnf(c_1052,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_28,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1060,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1064,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1693,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1060,c_1064])).

cnf(c_2422,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1052,c_28,c_1693])).

cnf(c_2423,plain,
    ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
    | v3_tdlat_3(X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2422])).

cnf(c_3321,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK1)) = iProver_top
    | v3_tdlat_3(sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_2423])).

cnf(c_20,negated_conjecture,
    ( v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_26,plain,
    ( v3_tdlat_3(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4428,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3321,c_24,c_26])).

cnf(c_3318,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_1060])).

cnf(c_3545,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3318,c_24])).

cnf(c_3549,plain,
    ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3545,c_1064])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(X0,X1)
    | r2_hidden(X0,u1_pre_topc(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1062,plain,
    ( v3_pre_topc(X0,X1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3637,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3549,c_1062])).

cnf(c_4178,plain,
    ( r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | v3_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3637,c_25])).

cnf(c_4179,plain,
    ( v3_pre_topc(X0,sK2) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4178])).

cnf(c_4437,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),X0),sK2) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
    | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4428,c_4179])).

cnf(c_15,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
    | v3_tdlat_3(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1055,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) != iProver_top
    | v3_tdlat_3(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5661,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2) != iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) != iProver_top
    | v3_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4437,c_1055])).

cnf(c_5666,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
    | v3_tdlat_3(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5661])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1197,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_3845,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(c_4585,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_3845])).

cnf(c_4587,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_4585])).

cnf(c_3322,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3304,c_1062])).

cnf(c_4193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | v3_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3322,c_24])).

cnf(c_4194,plain,
    ( v3_pre_topc(X0,sK1) != iProver_top
    | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4193])).

cnf(c_4200,plain,
    ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top
    | v3_tdlat_3(sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1053,c_4194])).

cnf(c_4562,plain,
    ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4200,c_25,c_27])).

cnf(c_4564,plain,
    ( ~ v3_pre_topc(sK0(sK2),sK1)
    | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4562])).

cnf(c_1620,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
    | k1_zfmisc_1(u1_struct_0(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),X2)
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X3)) != X2 ),
    inference(instantiation,[status(thm)],[c_1620])).

cnf(c_2278,plain,
    ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
    | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_3882,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
    inference(instantiation,[status(thm)],[c_2278])).

cnf(c_3889,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_3882])).

cnf(c_667,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2911,plain,
    ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_2912,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_2849,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2851,plain,
    ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_679,plain,
    ( X0 != X1
    | X2 != X3
    | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1468,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
    | sK0(sK2) != X1
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_679])).

cnf(c_1719,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1468])).

cnf(c_2501,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_1719])).

cnf(c_2502,plain,
    ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
    | sK0(sK2) != sK0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_2400,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2402,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2400])).

cnf(c_2176,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2175])).

cnf(c_2037,plain,
    ( sK0(sK2) = sK0(sK2) ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_671,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1483,plain,
    ( u1_struct_0(sK2) != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_1653,plain,
    ( u1_struct_0(sK2) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1654,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_1653])).

cnf(c_1429,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(X0,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1428])).

cnf(c_1431,plain,
    ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1429])).

cnf(c_1253,plain,
    ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | m1_pre_topc(sK1,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_1129,plain,
    ( ~ m1_pre_topc(sK2,X0)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_125])).

cnf(c_1131,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
    | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1129])).

cnf(c_673,plain,
    ( X0 != X1
    | u1_pre_topc(X0) = u1_pre_topc(X1) ),
    theory(equality)).

cnf(c_684,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_65,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_61,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_48,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_38,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21468,c_13660,c_9137,c_5778,c_5666,c_4587,c_4564,c_3889,c_2912,c_2851,c_2812,c_2502,c_2402,c_2176,c_2037,c_1654,c_1431,c_1430,c_1254,c_1253,c_1131,c_684,c_312,c_65,c_61,c_48,c_39,c_38,c_19,c_20,c_25,c_22,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.66/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.50  
% 7.66/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.50  
% 7.66/1.50  ------  iProver source info
% 7.66/1.50  
% 7.66/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.50  git: non_committed_changes: false
% 7.66/1.50  git: last_make_outside_of_git: false
% 7.66/1.50  
% 7.66/1.50  ------ 
% 7.66/1.50  
% 7.66/1.50  ------ Input Options
% 7.66/1.50  
% 7.66/1.50  --out_options                           all
% 7.66/1.50  --tptp_safe_out                         true
% 7.66/1.50  --problem_path                          ""
% 7.66/1.50  --include_path                          ""
% 7.66/1.50  --clausifier                            res/vclausify_rel
% 7.66/1.50  --clausifier_options                    ""
% 7.66/1.50  --stdin                                 false
% 7.66/1.50  --stats_out                             all
% 7.66/1.50  
% 7.66/1.50  ------ General Options
% 7.66/1.50  
% 7.66/1.50  --fof                                   false
% 7.66/1.50  --time_out_real                         305.
% 7.66/1.50  --time_out_virtual                      -1.
% 7.66/1.50  --symbol_type_check                     false
% 7.66/1.50  --clausify_out                          false
% 7.66/1.50  --sig_cnt_out                           false
% 7.66/1.50  --trig_cnt_out                          false
% 7.66/1.50  --trig_cnt_out_tolerance                1.
% 7.66/1.50  --trig_cnt_out_sk_spl                   false
% 7.66/1.50  --abstr_cl_out                          false
% 7.66/1.50  
% 7.66/1.50  ------ Global Options
% 7.66/1.50  
% 7.66/1.50  --schedule                              default
% 7.66/1.50  --add_important_lit                     false
% 7.66/1.50  --prop_solver_per_cl                    1000
% 7.66/1.50  --min_unsat_core                        false
% 7.66/1.50  --soft_assumptions                      false
% 7.66/1.50  --soft_lemma_size                       3
% 7.66/1.50  --prop_impl_unit_size                   0
% 7.66/1.50  --prop_impl_unit                        []
% 7.66/1.50  --share_sel_clauses                     true
% 7.66/1.50  --reset_solvers                         false
% 7.66/1.50  --bc_imp_inh                            [conj_cone]
% 7.66/1.50  --conj_cone_tolerance                   3.
% 7.66/1.50  --extra_neg_conj                        none
% 7.66/1.50  --large_theory_mode                     true
% 7.66/1.50  --prolific_symb_bound                   200
% 7.66/1.50  --lt_threshold                          2000
% 7.66/1.50  --clause_weak_htbl                      true
% 7.66/1.50  --gc_record_bc_elim                     false
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing Options
% 7.66/1.50  
% 7.66/1.50  --preprocessing_flag                    true
% 7.66/1.50  --time_out_prep_mult                    0.1
% 7.66/1.50  --splitting_mode                        input
% 7.66/1.50  --splitting_grd                         true
% 7.66/1.50  --splitting_cvd                         false
% 7.66/1.50  --splitting_cvd_svl                     false
% 7.66/1.50  --splitting_nvd                         32
% 7.66/1.50  --sub_typing                            true
% 7.66/1.50  --prep_gs_sim                           true
% 7.66/1.50  --prep_unflatten                        true
% 7.66/1.50  --prep_res_sim                          true
% 7.66/1.50  --prep_upred                            true
% 7.66/1.50  --prep_sem_filter                       exhaustive
% 7.66/1.50  --prep_sem_filter_out                   false
% 7.66/1.50  --pred_elim                             true
% 7.66/1.50  --res_sim_input                         true
% 7.66/1.50  --eq_ax_congr_red                       true
% 7.66/1.50  --pure_diseq_elim                       true
% 7.66/1.50  --brand_transform                       false
% 7.66/1.50  --non_eq_to_eq                          false
% 7.66/1.50  --prep_def_merge                        true
% 7.66/1.50  --prep_def_merge_prop_impl              false
% 7.66/1.50  --prep_def_merge_mbd                    true
% 7.66/1.50  --prep_def_merge_tr_red                 false
% 7.66/1.50  --prep_def_merge_tr_cl                  false
% 7.66/1.50  --smt_preprocessing                     true
% 7.66/1.50  --smt_ac_axioms                         fast
% 7.66/1.50  --preprocessed_out                      false
% 7.66/1.50  --preprocessed_stats                    false
% 7.66/1.50  
% 7.66/1.50  ------ Abstraction refinement Options
% 7.66/1.50  
% 7.66/1.50  --abstr_ref                             []
% 7.66/1.50  --abstr_ref_prep                        false
% 7.66/1.50  --abstr_ref_until_sat                   false
% 7.66/1.50  --abstr_ref_sig_restrict                funpre
% 7.66/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.50  --abstr_ref_under                       []
% 7.66/1.50  
% 7.66/1.50  ------ SAT Options
% 7.66/1.50  
% 7.66/1.50  --sat_mode                              false
% 7.66/1.50  --sat_fm_restart_options                ""
% 7.66/1.50  --sat_gr_def                            false
% 7.66/1.50  --sat_epr_types                         true
% 7.66/1.50  --sat_non_cyclic_types                  false
% 7.66/1.50  --sat_finite_models                     false
% 7.66/1.50  --sat_fm_lemmas                         false
% 7.66/1.50  --sat_fm_prep                           false
% 7.66/1.50  --sat_fm_uc_incr                        true
% 7.66/1.50  --sat_out_model                         small
% 7.66/1.50  --sat_out_clauses                       false
% 7.66/1.50  
% 7.66/1.50  ------ QBF Options
% 7.66/1.50  
% 7.66/1.50  --qbf_mode                              false
% 7.66/1.50  --qbf_elim_univ                         false
% 7.66/1.50  --qbf_dom_inst                          none
% 7.66/1.50  --qbf_dom_pre_inst                      false
% 7.66/1.50  --qbf_sk_in                             false
% 7.66/1.50  --qbf_pred_elim                         true
% 7.66/1.50  --qbf_split                             512
% 7.66/1.50  
% 7.66/1.50  ------ BMC1 Options
% 7.66/1.50  
% 7.66/1.50  --bmc1_incremental                      false
% 7.66/1.50  --bmc1_axioms                           reachable_all
% 7.66/1.50  --bmc1_min_bound                        0
% 7.66/1.50  --bmc1_max_bound                        -1
% 7.66/1.50  --bmc1_max_bound_default                -1
% 7.66/1.50  --bmc1_symbol_reachability              true
% 7.66/1.50  --bmc1_property_lemmas                  false
% 7.66/1.50  --bmc1_k_induction                      false
% 7.66/1.50  --bmc1_non_equiv_states                 false
% 7.66/1.50  --bmc1_deadlock                         false
% 7.66/1.50  --bmc1_ucm                              false
% 7.66/1.50  --bmc1_add_unsat_core                   none
% 7.66/1.50  --bmc1_unsat_core_children              false
% 7.66/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.50  --bmc1_out_stat                         full
% 7.66/1.50  --bmc1_ground_init                      false
% 7.66/1.50  --bmc1_pre_inst_next_state              false
% 7.66/1.50  --bmc1_pre_inst_state                   false
% 7.66/1.50  --bmc1_pre_inst_reach_state             false
% 7.66/1.50  --bmc1_out_unsat_core                   false
% 7.66/1.50  --bmc1_aig_witness_out                  false
% 7.66/1.50  --bmc1_verbose                          false
% 7.66/1.50  --bmc1_dump_clauses_tptp                false
% 7.66/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.50  --bmc1_dump_file                        -
% 7.66/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.50  --bmc1_ucm_extend_mode                  1
% 7.66/1.50  --bmc1_ucm_init_mode                    2
% 7.66/1.50  --bmc1_ucm_cone_mode                    none
% 7.66/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.50  --bmc1_ucm_relax_model                  4
% 7.66/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.50  --bmc1_ucm_layered_model                none
% 7.66/1.50  --bmc1_ucm_max_lemma_size               10
% 7.66/1.50  
% 7.66/1.50  ------ AIG Options
% 7.66/1.50  
% 7.66/1.50  --aig_mode                              false
% 7.66/1.50  
% 7.66/1.50  ------ Instantiation Options
% 7.66/1.50  
% 7.66/1.50  --instantiation_flag                    true
% 7.66/1.50  --inst_sos_flag                         true
% 7.66/1.50  --inst_sos_phase                        true
% 7.66/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.50  --inst_lit_sel_side                     num_symb
% 7.66/1.50  --inst_solver_per_active                1400
% 7.66/1.50  --inst_solver_calls_frac                1.
% 7.66/1.50  --inst_passive_queue_type               priority_queues
% 7.66/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.50  --inst_passive_queues_freq              [25;2]
% 7.66/1.50  --inst_dismatching                      true
% 7.66/1.50  --inst_eager_unprocessed_to_passive     true
% 7.66/1.50  --inst_prop_sim_given                   true
% 7.66/1.50  --inst_prop_sim_new                     false
% 7.66/1.50  --inst_subs_new                         false
% 7.66/1.50  --inst_eq_res_simp                      false
% 7.66/1.50  --inst_subs_given                       false
% 7.66/1.50  --inst_orphan_elimination               true
% 7.66/1.50  --inst_learning_loop_flag               true
% 7.66/1.50  --inst_learning_start                   3000
% 7.66/1.50  --inst_learning_factor                  2
% 7.66/1.50  --inst_start_prop_sim_after_learn       3
% 7.66/1.50  --inst_sel_renew                        solver
% 7.66/1.50  --inst_lit_activity_flag                true
% 7.66/1.50  --inst_restr_to_given                   false
% 7.66/1.50  --inst_activity_threshold               500
% 7.66/1.50  --inst_out_proof                        true
% 7.66/1.50  
% 7.66/1.50  ------ Resolution Options
% 7.66/1.50  
% 7.66/1.50  --resolution_flag                       true
% 7.66/1.50  --res_lit_sel                           adaptive
% 7.66/1.50  --res_lit_sel_side                      none
% 7.66/1.50  --res_ordering                          kbo
% 7.66/1.50  --res_to_prop_solver                    active
% 7.66/1.50  --res_prop_simpl_new                    false
% 7.66/1.50  --res_prop_simpl_given                  true
% 7.66/1.50  --res_passive_queue_type                priority_queues
% 7.66/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.50  --res_passive_queues_freq               [15;5]
% 7.66/1.50  --res_forward_subs                      full
% 7.66/1.50  --res_backward_subs                     full
% 7.66/1.50  --res_forward_subs_resolution           true
% 7.66/1.50  --res_backward_subs_resolution          true
% 7.66/1.50  --res_orphan_elimination                true
% 7.66/1.50  --res_time_limit                        2.
% 7.66/1.50  --res_out_proof                         true
% 7.66/1.50  
% 7.66/1.50  ------ Superposition Options
% 7.66/1.50  
% 7.66/1.50  --superposition_flag                    true
% 7.66/1.50  --sup_passive_queue_type                priority_queues
% 7.66/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.50  --demod_completeness_check              fast
% 7.66/1.50  --demod_use_ground                      true
% 7.66/1.50  --sup_to_prop_solver                    passive
% 7.66/1.50  --sup_prop_simpl_new                    true
% 7.66/1.50  --sup_prop_simpl_given                  true
% 7.66/1.50  --sup_fun_splitting                     true
% 7.66/1.50  --sup_smt_interval                      50000
% 7.66/1.50  
% 7.66/1.50  ------ Superposition Simplification Setup
% 7.66/1.50  
% 7.66/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.50  --sup_immed_triv                        [TrivRules]
% 7.66/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_immed_bw_main                     []
% 7.66/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_input_bw                          []
% 7.66/1.50  
% 7.66/1.50  ------ Combination Options
% 7.66/1.50  
% 7.66/1.50  --comb_res_mult                         3
% 7.66/1.50  --comb_sup_mult                         2
% 7.66/1.50  --comb_inst_mult                        10
% 7.66/1.50  
% 7.66/1.50  ------ Debug Options
% 7.66/1.50  
% 7.66/1.50  --dbg_backtrace                         false
% 7.66/1.50  --dbg_dump_prop_clauses                 false
% 7.66/1.50  --dbg_dump_prop_clauses_file            -
% 7.66/1.50  --dbg_out_stat                          false
% 7.66/1.50  ------ Parsing...
% 7.66/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.50  ------ Proving...
% 7.66/1.50  ------ Problem Properties 
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  clauses                                 22
% 7.66/1.50  conjectures                             5
% 7.66/1.50  EPR                                     8
% 7.66/1.50  Horn                                    20
% 7.66/1.50  unary                                   6
% 7.66/1.50  binary                                  2
% 7.66/1.50  lits                                    59
% 7.66/1.50  lits eq                                 2
% 7.66/1.50  fd_pure                                 0
% 7.66/1.50  fd_pseudo                               0
% 7.66/1.50  fd_cond                                 0
% 7.66/1.50  fd_pseudo_cond                          1
% 7.66/1.50  AC symbols                              0
% 7.66/1.50  
% 7.66/1.50  ------ Schedule dynamic 5 is on 
% 7.66/1.50  
% 7.66/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  ------ 
% 7.66/1.50  Current options:
% 7.66/1.50  ------ 
% 7.66/1.50  
% 7.66/1.50  ------ Input Options
% 7.66/1.50  
% 7.66/1.50  --out_options                           all
% 7.66/1.50  --tptp_safe_out                         true
% 7.66/1.50  --problem_path                          ""
% 7.66/1.50  --include_path                          ""
% 7.66/1.50  --clausifier                            res/vclausify_rel
% 7.66/1.50  --clausifier_options                    ""
% 7.66/1.50  --stdin                                 false
% 7.66/1.50  --stats_out                             all
% 7.66/1.50  
% 7.66/1.50  ------ General Options
% 7.66/1.50  
% 7.66/1.50  --fof                                   false
% 7.66/1.50  --time_out_real                         305.
% 7.66/1.50  --time_out_virtual                      -1.
% 7.66/1.50  --symbol_type_check                     false
% 7.66/1.50  --clausify_out                          false
% 7.66/1.50  --sig_cnt_out                           false
% 7.66/1.50  --trig_cnt_out                          false
% 7.66/1.50  --trig_cnt_out_tolerance                1.
% 7.66/1.50  --trig_cnt_out_sk_spl                   false
% 7.66/1.50  --abstr_cl_out                          false
% 7.66/1.50  
% 7.66/1.50  ------ Global Options
% 7.66/1.50  
% 7.66/1.50  --schedule                              default
% 7.66/1.50  --add_important_lit                     false
% 7.66/1.50  --prop_solver_per_cl                    1000
% 7.66/1.50  --min_unsat_core                        false
% 7.66/1.50  --soft_assumptions                      false
% 7.66/1.50  --soft_lemma_size                       3
% 7.66/1.50  --prop_impl_unit_size                   0
% 7.66/1.50  --prop_impl_unit                        []
% 7.66/1.50  --share_sel_clauses                     true
% 7.66/1.50  --reset_solvers                         false
% 7.66/1.50  --bc_imp_inh                            [conj_cone]
% 7.66/1.50  --conj_cone_tolerance                   3.
% 7.66/1.50  --extra_neg_conj                        none
% 7.66/1.50  --large_theory_mode                     true
% 7.66/1.50  --prolific_symb_bound                   200
% 7.66/1.50  --lt_threshold                          2000
% 7.66/1.50  --clause_weak_htbl                      true
% 7.66/1.50  --gc_record_bc_elim                     false
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing Options
% 7.66/1.50  
% 7.66/1.50  --preprocessing_flag                    true
% 7.66/1.50  --time_out_prep_mult                    0.1
% 7.66/1.50  --splitting_mode                        input
% 7.66/1.50  --splitting_grd                         true
% 7.66/1.50  --splitting_cvd                         false
% 7.66/1.50  --splitting_cvd_svl                     false
% 7.66/1.50  --splitting_nvd                         32
% 7.66/1.50  --sub_typing                            true
% 7.66/1.50  --prep_gs_sim                           true
% 7.66/1.50  --prep_unflatten                        true
% 7.66/1.50  --prep_res_sim                          true
% 7.66/1.50  --prep_upred                            true
% 7.66/1.50  --prep_sem_filter                       exhaustive
% 7.66/1.50  --prep_sem_filter_out                   false
% 7.66/1.50  --pred_elim                             true
% 7.66/1.50  --res_sim_input                         true
% 7.66/1.50  --eq_ax_congr_red                       true
% 7.66/1.50  --pure_diseq_elim                       true
% 7.66/1.50  --brand_transform                       false
% 7.66/1.50  --non_eq_to_eq                          false
% 7.66/1.50  --prep_def_merge                        true
% 7.66/1.50  --prep_def_merge_prop_impl              false
% 7.66/1.50  --prep_def_merge_mbd                    true
% 7.66/1.50  --prep_def_merge_tr_red                 false
% 7.66/1.50  --prep_def_merge_tr_cl                  false
% 7.66/1.50  --smt_preprocessing                     true
% 7.66/1.50  --smt_ac_axioms                         fast
% 7.66/1.50  --preprocessed_out                      false
% 7.66/1.50  --preprocessed_stats                    false
% 7.66/1.50  
% 7.66/1.50  ------ Abstraction refinement Options
% 7.66/1.50  
% 7.66/1.50  --abstr_ref                             []
% 7.66/1.50  --abstr_ref_prep                        false
% 7.66/1.50  --abstr_ref_until_sat                   false
% 7.66/1.50  --abstr_ref_sig_restrict                funpre
% 7.66/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.50  --abstr_ref_under                       []
% 7.66/1.50  
% 7.66/1.50  ------ SAT Options
% 7.66/1.50  
% 7.66/1.50  --sat_mode                              false
% 7.66/1.50  --sat_fm_restart_options                ""
% 7.66/1.50  --sat_gr_def                            false
% 7.66/1.50  --sat_epr_types                         true
% 7.66/1.50  --sat_non_cyclic_types                  false
% 7.66/1.50  --sat_finite_models                     false
% 7.66/1.50  --sat_fm_lemmas                         false
% 7.66/1.50  --sat_fm_prep                           false
% 7.66/1.50  --sat_fm_uc_incr                        true
% 7.66/1.50  --sat_out_model                         small
% 7.66/1.50  --sat_out_clauses                       false
% 7.66/1.50  
% 7.66/1.50  ------ QBF Options
% 7.66/1.50  
% 7.66/1.50  --qbf_mode                              false
% 7.66/1.50  --qbf_elim_univ                         false
% 7.66/1.50  --qbf_dom_inst                          none
% 7.66/1.50  --qbf_dom_pre_inst                      false
% 7.66/1.50  --qbf_sk_in                             false
% 7.66/1.50  --qbf_pred_elim                         true
% 7.66/1.50  --qbf_split                             512
% 7.66/1.50  
% 7.66/1.50  ------ BMC1 Options
% 7.66/1.50  
% 7.66/1.50  --bmc1_incremental                      false
% 7.66/1.50  --bmc1_axioms                           reachable_all
% 7.66/1.50  --bmc1_min_bound                        0
% 7.66/1.50  --bmc1_max_bound                        -1
% 7.66/1.50  --bmc1_max_bound_default                -1
% 7.66/1.50  --bmc1_symbol_reachability              true
% 7.66/1.50  --bmc1_property_lemmas                  false
% 7.66/1.50  --bmc1_k_induction                      false
% 7.66/1.50  --bmc1_non_equiv_states                 false
% 7.66/1.50  --bmc1_deadlock                         false
% 7.66/1.50  --bmc1_ucm                              false
% 7.66/1.50  --bmc1_add_unsat_core                   none
% 7.66/1.50  --bmc1_unsat_core_children              false
% 7.66/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.50  --bmc1_out_stat                         full
% 7.66/1.50  --bmc1_ground_init                      false
% 7.66/1.50  --bmc1_pre_inst_next_state              false
% 7.66/1.50  --bmc1_pre_inst_state                   false
% 7.66/1.50  --bmc1_pre_inst_reach_state             false
% 7.66/1.50  --bmc1_out_unsat_core                   false
% 7.66/1.50  --bmc1_aig_witness_out                  false
% 7.66/1.50  --bmc1_verbose                          false
% 7.66/1.50  --bmc1_dump_clauses_tptp                false
% 7.66/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.50  --bmc1_dump_file                        -
% 7.66/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.50  --bmc1_ucm_extend_mode                  1
% 7.66/1.50  --bmc1_ucm_init_mode                    2
% 7.66/1.50  --bmc1_ucm_cone_mode                    none
% 7.66/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.50  --bmc1_ucm_relax_model                  4
% 7.66/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.50  --bmc1_ucm_layered_model                none
% 7.66/1.50  --bmc1_ucm_max_lemma_size               10
% 7.66/1.50  
% 7.66/1.50  ------ AIG Options
% 7.66/1.50  
% 7.66/1.50  --aig_mode                              false
% 7.66/1.50  
% 7.66/1.50  ------ Instantiation Options
% 7.66/1.50  
% 7.66/1.50  --instantiation_flag                    true
% 7.66/1.50  --inst_sos_flag                         true
% 7.66/1.50  --inst_sos_phase                        true
% 7.66/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.50  --inst_lit_sel_side                     none
% 7.66/1.50  --inst_solver_per_active                1400
% 7.66/1.50  --inst_solver_calls_frac                1.
% 7.66/1.50  --inst_passive_queue_type               priority_queues
% 7.66/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.50  --inst_passive_queues_freq              [25;2]
% 7.66/1.50  --inst_dismatching                      true
% 7.66/1.50  --inst_eager_unprocessed_to_passive     true
% 7.66/1.50  --inst_prop_sim_given                   true
% 7.66/1.50  --inst_prop_sim_new                     false
% 7.66/1.50  --inst_subs_new                         false
% 7.66/1.50  --inst_eq_res_simp                      false
% 7.66/1.50  --inst_subs_given                       false
% 7.66/1.50  --inst_orphan_elimination               true
% 7.66/1.50  --inst_learning_loop_flag               true
% 7.66/1.50  --inst_learning_start                   3000
% 7.66/1.50  --inst_learning_factor                  2
% 7.66/1.50  --inst_start_prop_sim_after_learn       3
% 7.66/1.50  --inst_sel_renew                        solver
% 7.66/1.50  --inst_lit_activity_flag                true
% 7.66/1.50  --inst_restr_to_given                   false
% 7.66/1.50  --inst_activity_threshold               500
% 7.66/1.50  --inst_out_proof                        true
% 7.66/1.50  
% 7.66/1.50  ------ Resolution Options
% 7.66/1.50  
% 7.66/1.50  --resolution_flag                       false
% 7.66/1.50  --res_lit_sel                           adaptive
% 7.66/1.50  --res_lit_sel_side                      none
% 7.66/1.50  --res_ordering                          kbo
% 7.66/1.50  --res_to_prop_solver                    active
% 7.66/1.50  --res_prop_simpl_new                    false
% 7.66/1.50  --res_prop_simpl_given                  true
% 7.66/1.50  --res_passive_queue_type                priority_queues
% 7.66/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.50  --res_passive_queues_freq               [15;5]
% 7.66/1.50  --res_forward_subs                      full
% 7.66/1.50  --res_backward_subs                     full
% 7.66/1.50  --res_forward_subs_resolution           true
% 7.66/1.50  --res_backward_subs_resolution          true
% 7.66/1.50  --res_orphan_elimination                true
% 7.66/1.50  --res_time_limit                        2.
% 7.66/1.50  --res_out_proof                         true
% 7.66/1.50  
% 7.66/1.50  ------ Superposition Options
% 7.66/1.50  
% 7.66/1.50  --superposition_flag                    true
% 7.66/1.50  --sup_passive_queue_type                priority_queues
% 7.66/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.50  --demod_completeness_check              fast
% 7.66/1.50  --demod_use_ground                      true
% 7.66/1.50  --sup_to_prop_solver                    passive
% 7.66/1.50  --sup_prop_simpl_new                    true
% 7.66/1.50  --sup_prop_simpl_given                  true
% 7.66/1.50  --sup_fun_splitting                     true
% 7.66/1.50  --sup_smt_interval                      50000
% 7.66/1.50  
% 7.66/1.50  ------ Superposition Simplification Setup
% 7.66/1.50  
% 7.66/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.50  --sup_immed_triv                        [TrivRules]
% 7.66/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_immed_bw_main                     []
% 7.66/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.50  --sup_input_bw                          []
% 7.66/1.50  
% 7.66/1.50  ------ Combination Options
% 7.66/1.50  
% 7.66/1.50  --comb_res_mult                         3
% 7.66/1.50  --comb_sup_mult                         2
% 7.66/1.50  --comb_inst_mult                        10
% 7.66/1.50  
% 7.66/1.50  ------ Debug Options
% 7.66/1.50  
% 7.66/1.50  --dbg_backtrace                         false
% 7.66/1.50  --dbg_dump_prop_clauses                 false
% 7.66/1.50  --dbg_dump_prop_clauses_file            -
% 7.66/1.50  --dbg_out_stat                          false
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  ------ Proving...
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  % SZS status Theorem for theBenchmark.p
% 7.66/1.50  
% 7.66/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.50  
% 7.66/1.50  fof(f2,axiom,(
% 7.66/1.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f15,plain,(
% 7.66/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.66/1.50    inference(ennf_transformation,[],[f2])).
% 7.66/1.50  
% 7.66/1.50  fof(f16,plain,(
% 7.66/1.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.66/1.50    inference(flattening,[],[f15])).
% 7.66/1.50  
% 7.66/1.50  fof(f45,plain,(
% 7.66/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f16])).
% 7.66/1.50  
% 7.66/1.50  fof(f12,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f27,plain,(
% 7.66/1.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f12])).
% 7.66/1.50  
% 7.66/1.50  fof(f28,plain,(
% 7.66/1.50    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(flattening,[],[f27])).
% 7.66/1.50  
% 7.66/1.50  fof(f35,plain,(
% 7.66/1.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(nnf_transformation,[],[f28])).
% 7.66/1.50  
% 7.66/1.50  fof(f36,plain,(
% 7.66/1.50    ! [X0] : (((v3_tdlat_3(X0) | ? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(rectify,[],[f35])).
% 7.66/1.50  
% 7.66/1.50  fof(f37,plain,(
% 7.66/1.50    ! [X0] : (? [X1] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.66/1.50    introduced(choice_axiom,[])).
% 7.66/1.50  
% 7.66/1.50  fof(f38,plain,(
% 7.66/1.50    ! [X0] : (((v3_tdlat_3(X0) | (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) & r2_hidden(sK0(X0),u1_pre_topc(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_tdlat_3(X0))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 7.66/1.50  
% 7.66/1.50  fof(f57,plain,(
% 7.66/1.50    ( ! [X2,X0] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f38])).
% 7.66/1.50  
% 7.66/1.50  fof(f10,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f25,plain,(
% 7.66/1.50    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f10])).
% 7.66/1.50  
% 7.66/1.50  fof(f55,plain,(
% 7.66/1.50    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f25])).
% 7.66/1.50  
% 7.66/1.50  fof(f8,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f22,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f8])).
% 7.66/1.50  
% 7.66/1.50  fof(f34,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(nnf_transformation,[],[f22])).
% 7.66/1.50  
% 7.66/1.50  fof(f52,plain,(
% 7.66/1.50    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f34])).
% 7.66/1.50  
% 7.66/1.50  fof(f4,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f18,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f4])).
% 7.66/1.50  
% 7.66/1.50  fof(f48,plain,(
% 7.66/1.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f18])).
% 7.66/1.50  
% 7.66/1.50  fof(f13,conjecture,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f14,negated_conjecture,(
% 7.66/1.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 7.66/1.50    inference(negated_conjecture,[],[f13])).
% 7.66/1.50  
% 7.66/1.50  fof(f29,plain,(
% 7.66/1.50    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f14])).
% 7.66/1.50  
% 7.66/1.50  fof(f30,plain,(
% 7.66/1.50    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 7.66/1.50    inference(flattening,[],[f29])).
% 7.66/1.50  
% 7.66/1.50  fof(f40,plain,(
% 7.66/1.50    ( ! [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) => (~v3_tdlat_3(sK2) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & l1_pre_topc(sK2))) )),
% 7.66/1.50    introduced(choice_axiom,[])).
% 7.66/1.50  
% 7.66/1.50  fof(f39,plain,(
% 7.66/1.50    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 7.66/1.50    introduced(choice_axiom,[])).
% 7.66/1.50  
% 7.66/1.50  fof(f41,plain,(
% 7.66/1.50    (~v3_tdlat_3(sK2) & v3_tdlat_3(sK1) & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 7.66/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f40,f39])).
% 7.66/1.50  
% 7.66/1.50  fof(f63,plain,(
% 7.66/1.50    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 7.66/1.50    inference(cnf_transformation,[],[f41])).
% 7.66/1.50  
% 7.66/1.50  fof(f7,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f21,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f7])).
% 7.66/1.50  
% 7.66/1.50  fof(f51,plain,(
% 7.66/1.50    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f21])).
% 7.66/1.50  
% 7.66/1.50  fof(f61,plain,(
% 7.66/1.50    l1_pre_topc(sK1)),
% 7.66/1.50    inference(cnf_transformation,[],[f41])).
% 7.66/1.50  
% 7.66/1.50  fof(f62,plain,(
% 7.66/1.50    l1_pre_topc(sK2)),
% 7.66/1.50    inference(cnf_transformation,[],[f41])).
% 7.66/1.50  
% 7.66/1.50  fof(f11,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f26,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f11])).
% 7.66/1.50  
% 7.66/1.50  fof(f56,plain,(
% 7.66/1.50    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f26])).
% 7.66/1.50  
% 7.66/1.50  fof(f1,axiom,(
% 7.66/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f31,plain,(
% 7.66/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.50    inference(nnf_transformation,[],[f1])).
% 7.66/1.50  
% 7.66/1.50  fof(f32,plain,(
% 7.66/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.50    inference(flattening,[],[f31])).
% 7.66/1.50  
% 7.66/1.50  fof(f44,plain,(
% 7.66/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f32])).
% 7.66/1.50  
% 7.66/1.50  fof(f58,plain,(
% 7.66/1.50    ( ! [X0] : (v3_tdlat_3(X0) | m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f38])).
% 7.66/1.50  
% 7.66/1.50  fof(f6,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f20,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f6])).
% 7.66/1.50  
% 7.66/1.50  fof(f50,plain,(
% 7.66/1.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f20])).
% 7.66/1.50  
% 7.66/1.50  fof(f65,plain,(
% 7.66/1.50    ~v3_tdlat_3(sK2)),
% 7.66/1.50    inference(cnf_transformation,[],[f41])).
% 7.66/1.50  
% 7.66/1.50  fof(f9,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f23,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f9])).
% 7.66/1.50  
% 7.66/1.50  fof(f24,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(flattening,[],[f23])).
% 7.66/1.50  
% 7.66/1.50  fof(f54,plain,(
% 7.66/1.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f24])).
% 7.66/1.50  
% 7.66/1.50  fof(f68,plain,(
% 7.66/1.50    ( ! [X2,X0,X3] : (v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(equality_resolution,[],[f54])).
% 7.66/1.50  
% 7.66/1.50  fof(f59,plain,(
% 7.66/1.50    ( ! [X0] : (v3_tdlat_3(X0) | r2_hidden(sK0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f38])).
% 7.66/1.50  
% 7.66/1.50  fof(f3,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f17,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f3])).
% 7.66/1.50  
% 7.66/1.50  fof(f33,plain,(
% 7.66/1.50    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(nnf_transformation,[],[f17])).
% 7.66/1.50  
% 7.66/1.50  fof(f47,plain,(
% 7.66/1.50    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f33])).
% 7.66/1.50  
% 7.66/1.50  fof(f5,axiom,(
% 7.66/1.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.66/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.50  
% 7.66/1.50  fof(f19,plain,(
% 7.66/1.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.66/1.50    inference(ennf_transformation,[],[f5])).
% 7.66/1.50  
% 7.66/1.50  fof(f49,plain,(
% 7.66/1.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f19])).
% 7.66/1.50  
% 7.66/1.50  fof(f64,plain,(
% 7.66/1.50    v3_tdlat_3(sK1)),
% 7.66/1.50    inference(cnf_transformation,[],[f41])).
% 7.66/1.50  
% 7.66/1.50  fof(f46,plain,(
% 7.66/1.50    ( ! [X0,X1] : (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f33])).
% 7.66/1.50  
% 7.66/1.50  fof(f60,plain,(
% 7.66/1.50    ( ! [X0] : (v3_tdlat_3(X0) | ~r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 7.66/1.50    inference(cnf_transformation,[],[f38])).
% 7.66/1.50  
% 7.66/1.50  fof(f42,plain,(
% 7.66/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.66/1.50    inference(cnf_transformation,[],[f32])).
% 7.66/1.50  
% 7.66/1.50  fof(f67,plain,(
% 7.66/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.66/1.50    inference(equality_resolution,[],[f42])).
% 7.66/1.50  
% 7.66/1.50  cnf(c_672,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.66/1.50      theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1821,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,X1)
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
% 7.66/1.50      | X2 != X1
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_672]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2252,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(X0,X1),X2)
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X3)
% 7.66/1.50      | X3 != X2
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1821]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3883,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),X1)
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X2)
% 7.66/1.50      | X2 != X1
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2252]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_13672,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X1)
% 7.66/1.50      | X1 != u1_pre_topc(X0)
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_3883]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_21466,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X1))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.66/1.50      | u1_pre_topc(X1) != u1_pre_topc(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_13672]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_21468,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.66/1.50      | u1_pre_topc(sK1) != u1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_21466]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,X1)
% 7.66/1.50      | m1_subset_1(X0,X2)
% 7.66/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 7.66/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1878,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,X1)
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2486,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | ~ m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1878]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3164,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2486]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_13658,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_3164]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_13660,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_13658]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_18,plain,
% 7.66/1.50      ( ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1))
% 7.66/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ v3_tdlat_3(X1)
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_9122,plain,
% 7.66/1.50      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(sK2)),u1_pre_topc(X0))
% 7.66/1.50      | ~ r2_hidden(sK0(sK2),u1_pre_topc(X0))
% 7.66/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ v3_tdlat_3(X0)
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_9137,plain,
% 7.66/1.50      ( r2_hidden(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),u1_pre_topc(sK1))
% 7.66/1.50      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 7.66/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | ~ v3_tdlat_3(sK1)
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_9122]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_13,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1057,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_11,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X0)
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_6,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_129,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.66/1.50      | ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_11,c_6]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_130,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_129]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1046,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_130]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_21,negated_conjecture,
% 7.66/1.50      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 7.66/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_9,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1058,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) = iProver_top
% 7.66/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1807,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK1) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_21,c_1058]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_23,negated_conjecture,
% 7.66/1.50      ( l1_pre_topc(sK1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_24,plain,
% 7.66/1.50      ( l1_pre_topc(sK1) = iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1911,plain,
% 7.66/1.50      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.66/1.50      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_1807,c_24]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1912,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_1911]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1917,plain,
% 7.66/1.50      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK2) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1046,c_1912]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_22,negated_conjecture,
% 7.66/1.50      ( l1_pre_topc(sK2) ),
% 7.66/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_25,plain,
% 7.66/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2169,plain,
% 7.66/1.50      ( m1_pre_topc(X0,sK2) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK1) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_1917,c_25]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2170,plain,
% 7.66/1.50      ( m1_pre_topc(X0,sK1) = iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK2) != iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_2169]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2175,plain,
% 7.66/1.50      ( m1_pre_topc(sK2,sK1) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1057,c_2170]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2357,plain,
% 7.66/1.50      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_2175,c_25]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_14,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1056,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_0,plain,
% 7.66/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.66/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1066,plain,
% 7.66/1.50      ( X0 = X1
% 7.66/1.50      | r1_tarski(X0,X1) != iProver_top
% 7.66/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1631,plain,
% 7.66/1.50      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.66/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.66/1.50      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1056,c_1066]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2574,plain,
% 7.66/1.50      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.66/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1056,c_1631]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_50,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X0) = iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2805,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.66/1.50      | u1_struct_0(X0) = u1_struct_0(X1)
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_2574,c_50]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2806,plain,
% 7.66/1.50      ( u1_struct_0(X0) = u1_struct_0(X1)
% 7.66/1.50      | m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | m1_pre_topc(X1,X0) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_2805]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2812,plain,
% 7.66/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 7.66/1.50      | m1_pre_topc(sK1,sK2) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_2357,c_2806]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_37,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X0) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_39,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,sK1) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_37]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1251,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.66/1.50      | m1_pre_topc(X0,sK2)
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1252,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_1251]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1254,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 7.66/1.50      | m1_pre_topc(sK1,sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1428,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.66/1.50      | m1_pre_topc(X0,sK1) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_21,c_1046]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1430,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 7.66/1.50      | m1_pre_topc(sK1,sK1) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1428]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3304,plain,
% 7.66/1.50      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_2812,c_24,c_25,c_39,c_1254,c_1430]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_17,plain,
% 7.66/1.50      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | v3_tdlat_3(X0)
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1053,plain,
% 7.66/1.50      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.66/1.50      | v3_tdlat_3(X0) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_8,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1059,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3313,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.66/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_1059]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4394,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.66/1.50      | v3_tdlat_3(sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1053,c_3313]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_19,negated_conjecture,
% 7.66/1.50      ( ~ v3_tdlat_3(sK2) ),
% 7.66/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_27,plain,
% 7.66/1.50      ( v3_tdlat_3(sK2) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4698,plain,
% 7.66/1.50      ( l1_pre_topc(X0) != iProver_top
% 7.66/1.50      | m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_4394,c_25,c_27]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4699,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_4698]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4704,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,sK1) != iProver_top
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_4699]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_311,plain,
% 7.66/1.50      ( m1_subset_1(sK0(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ l1_pre_topc(X0)
% 7.66/1.50      | sK2 != X0 ),
% 7.66/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_19]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_312,plain,
% 7.66/1.50      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(unflattening,[status(thm)],[c_311]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_313,plain,
% 7.66/1.50      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_312]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4831,plain,
% 7.66/1.50      ( m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_4704,c_25,c_313]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_12,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ v3_pre_topc(X2,X1)
% 7.66/1.50      | v3_pre_topc(X2,X0)
% 7.66/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_124,plain,
% 7.66/1.50      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | v3_pre_topc(X2,X0)
% 7.66/1.50      | ~ v3_pre_topc(X2,X1)
% 7.66/1.50      | ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_12,c_8]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_125,plain,
% 7.66/1.50      ( ~ m1_pre_topc(X0,X1)
% 7.66/1.50      | ~ v3_pre_topc(X2,X1)
% 7.66/1.50      | v3_pre_topc(X2,X0)
% 7.66/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_124]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1047,plain,
% 7.66/1.50      ( m1_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | v3_pre_topc(X2,X1) != iProver_top
% 7.66/1.50      | v3_pre_topc(X2,X0) = iProver_top
% 7.66/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_125]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4838,plain,
% 7.66/1.50      ( m1_pre_topc(sK2,X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(sK0(sK2),X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(sK0(sK2),sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_4831,c_1047]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_16,plain,
% 7.66/1.50      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 7.66/1.50      | v3_tdlat_3(X0)
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_322,plain,
% 7.66/1.50      ( r2_hidden(sK0(X0),u1_pre_topc(X0))
% 7.66/1.50      | ~ l1_pre_topc(X0)
% 7.66/1.50      | sK2 != X0 ),
% 7.66/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_323,plain,
% 7.66/1.50      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(unflattening,[status(thm)],[c_322]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_324,plain,
% 7.66/1.50      ( r2_hidden(sK0(sK2),u1_pre_topc(sK2)) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4,plain,
% 7.66/1.50      ( v3_pre_topc(X0,X1)
% 7.66/1.50      | ~ r2_hidden(X0,u1_pre_topc(X1))
% 7.66/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1859,plain,
% 7.66/1.50      ( v3_pre_topc(X0,sK2)
% 7.66/1.50      | ~ r2_hidden(X0,u1_pre_topc(sK2))
% 7.66/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2384,plain,
% 7.66/1.50      ( v3_pre_topc(sK0(sK2),sK2)
% 7.66/1.50      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK2))
% 7.66/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1859]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2385,plain,
% 7.66/1.50      ( v3_pre_topc(sK0(sK2),sK2) = iProver_top
% 7.66/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK2)) != iProver_top
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_2384]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5671,plain,
% 7.66/1.50      ( v3_pre_topc(sK0(sK2),sK2) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_4838,c_25,c_313,c_324,c_2385]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3314,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(X1,X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(X1,sK1) = iProver_top
% 7.66/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_1047]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4840,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(sK0(sK2),X0) != iProver_top
% 7.66/1.50      | v3_pre_topc(sK0(sK2),sK1) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_4831,c_3314]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5777,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,sK2) != iProver_top
% 7.66/1.50      | v3_pre_topc(sK0(sK2),sK1) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_5671,c_4840]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5778,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK1,sK2)
% 7.66/1.50      | v3_pre_topc(sK0(sK2),sK1)
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5777]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1052,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.66/1.50      | v3_tdlat_3(X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_28,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.66/1.50      | v3_tdlat_3(X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_7,plain,
% 7.66/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1060,plain,
% 7.66/1.50      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1064,plain,
% 7.66/1.50      ( r2_hidden(X0,X1) != iProver_top
% 7.66/1.50      | m1_subset_1(X0,X2) = iProver_top
% 7.66/1.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1693,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1060,c_1064]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2422,plain,
% 7.66/1.50      ( r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.66/1.50      | v3_tdlat_3(X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_1052,c_28,c_1693]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2423,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(X1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(X1),X0),u1_pre_topc(X1)) = iProver_top
% 7.66/1.50      | v3_tdlat_3(X1) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_2422]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3321,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK1)) = iProver_top
% 7.66/1.50      | v3_tdlat_3(sK1) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_2423]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_20,negated_conjecture,
% 7.66/1.50      ( v3_tdlat_3(sK1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_26,plain,
% 7.66/1.50      ( v3_tdlat_3(sK1) = iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4428,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK1)) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_3321,c_24,c_26]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3318,plain,
% 7.66/1.50      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_1060]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3545,plain,
% 7.66/1.50      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_3318,c_24]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3549,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3545,c_1064]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5,plain,
% 7.66/1.50      ( ~ v3_pre_topc(X0,X1)
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(X1))
% 7.66/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | ~ l1_pre_topc(X1) ),
% 7.66/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1062,plain,
% 7.66/1.50      ( v3_pre_topc(X0,X1) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(X1)) = iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 7.66/1.50      | l1_pre_topc(X1) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3637,plain,
% 7.66/1.50      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3549,c_1062]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4178,plain,
% 7.66/1.50      ( r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | v3_pre_topc(X0,sK2) != iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_3637,c_25]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4179,plain,
% 7.66/1.50      ( v3_pre_topc(X0,sK2) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK2)) = iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_4178]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4437,plain,
% 7.66/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),X0),sK2) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | r2_hidden(k6_subset_1(u1_struct_0(sK2),X0),u1_pre_topc(sK2)) = iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_4428,c_4179]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_15,plain,
% 7.66/1.50      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0))
% 7.66/1.50      | v3_tdlat_3(X0)
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1055,plain,
% 7.66/1.50      ( r2_hidden(k6_subset_1(u1_struct_0(X0),sK0(X0)),u1_pre_topc(X0)) != iProver_top
% 7.66/1.50      | v3_tdlat_3(X0) = iProver_top
% 7.66/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.66/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5661,plain,
% 7.66/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2) != iProver_top
% 7.66/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) != iProver_top
% 7.66/1.50      | v3_tdlat_3(sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_4437,c_1055]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_5666,plain,
% 7.66/1.50      ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.66/1.50      | ~ r2_hidden(sK0(sK2),u1_pre_topc(sK1))
% 7.66/1.50      | v3_tdlat_3(sK2)
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_5661]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_670,plain,
% 7.66/1.50      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.66/1.50      theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1197,plain,
% 7.66/1.50      ( ~ m1_subset_1(X0,X1)
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != X1 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_670]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1298,plain,
% 7.66/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(X1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1197]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3845,plain,
% 7.66/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1298]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4585,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_3845]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4587,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_4585]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3322,plain,
% 7.66/1.50      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.66/1.50      | l1_pre_topc(sK1) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_3304,c_1062]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4193,plain,
% 7.66/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.66/1.50      | v3_pre_topc(X0,sK1) != iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_3322,c_24]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4194,plain,
% 7.66/1.50      ( v3_pre_topc(X0,sK1) != iProver_top
% 7.66/1.50      | r2_hidden(X0,u1_pre_topc(sK1)) = iProver_top
% 7.66/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.66/1.50      inference(renaming,[status(thm)],[c_4193]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4200,plain,
% 7.66/1.50      ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
% 7.66/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top
% 7.66/1.50      | v3_tdlat_3(sK2) = iProver_top
% 7.66/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.66/1.50      inference(superposition,[status(thm)],[c_1053,c_4194]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4562,plain,
% 7.66/1.50      ( v3_pre_topc(sK0(sK2),sK1) != iProver_top
% 7.66/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) = iProver_top ),
% 7.66/1.50      inference(global_propositional_subsumption,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_4200,c_25,c_27]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_4564,plain,
% 7.66/1.50      ( ~ v3_pre_topc(sK0(sK2),sK1)
% 7.66/1.50      | r2_hidden(sK0(sK2),u1_pre_topc(sK1)) ),
% 7.66/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4562]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1620,plain,
% 7.66/1.50      ( ~ m1_subset_1(X0,X1)
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != X0
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(X2)) != X1 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_670]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1837,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),X2)
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X3)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(X3)) != X2 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1620]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2278,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X2)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(X0,X1)
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(X2)) != k1_zfmisc_1(u1_struct_0(X2)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1837]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3882,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(X0),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X1)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2278]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_3889,plain,
% 7.66/1.50      ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK1),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | k6_subset_1(u1_struct_0(sK2),sK0(sK2)) != k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_3882]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_667,plain,( X0 = X0 ),theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2911,plain,
% 7.66/1.50      ( k1_zfmisc_1(u1_struct_0(X0)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_667]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2912,plain,
% 7.66/1.50      ( k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2911]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2849,plain,
% 7.66/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
% 7.66/1.50      | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(X0))
% 7.66/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2851,plain,
% 7.66/1.50      ( v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
% 7.66/1.50      | ~ r2_hidden(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),u1_pre_topc(sK1))
% 7.66/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2849]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_679,plain,
% 7.66/1.50      ( X0 != X1 | X2 != X3 | k6_subset_1(X0,X2) = k6_subset_1(X1,X3) ),
% 7.66/1.50      theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1468,plain,
% 7.66/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,X1)
% 7.66/1.50      | sK0(sK2) != X1
% 7.66/1.50      | u1_struct_0(sK2) != X0 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_679]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1719,plain,
% 7.66/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(X0,sK0(sK2))
% 7.66/1.50      | sK0(sK2) != sK0(sK2)
% 7.66/1.50      | u1_struct_0(sK2) != X0 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1468]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2501,plain,
% 7.66/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(X0),sK0(sK2))
% 7.66/1.50      | sK0(sK2) != sK0(sK2)
% 7.66/1.50      | u1_struct_0(sK2) != u1_struct_0(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1719]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2502,plain,
% 7.66/1.50      ( k6_subset_1(u1_struct_0(sK2),sK0(sK2)) = k6_subset_1(u1_struct_0(sK1),sK0(sK2))
% 7.66/1.50      | sK0(sK2) != sK0(sK2)
% 7.66/1.50      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2501]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2400,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK2,X0)
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(X0)))
% 7.66/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2402,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK2,sK1)
% 7.66/1.50      | m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.66/1.50      | ~ m1_subset_1(sK0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2400]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2176,plain,
% 7.66/1.50      ( m1_pre_topc(sK2,sK1) | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_2175]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2037,plain,
% 7.66/1.50      ( sK0(sK2) = sK0(sK2) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_667]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_671,plain,
% 7.66/1.50      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 7.66/1.50      theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1483,plain,
% 7.66/1.50      ( u1_struct_0(sK2) != X0
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_671]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1653,plain,
% 7.66/1.50      ( u1_struct_0(sK2) != u1_struct_0(X0)
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(X0)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1483]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1654,plain,
% 7.66/1.50      ( u1_struct_0(sK2) != u1_struct_0(sK1)
% 7.66/1.50      | k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK1)) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1653]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1429,plain,
% 7.66/1.50      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.66/1.50      | ~ m1_pre_topc(X0,sK1)
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_1428]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1431,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.66/1.50      | ~ m1_pre_topc(sK1,sK1)
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1429]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1253,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
% 7.66/1.50      | m1_pre_topc(sK1,sK2)
% 7.66/1.50      | ~ l1_pre_topc(sK2) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1251]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1129,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK2,X0)
% 7.66/1.50      | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),X0)
% 7.66/1.50      | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.66/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(X0) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_125]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_1131,plain,
% 7.66/1.50      ( ~ m1_pre_topc(sK2,sK1)
% 7.66/1.50      | ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK1)
% 7.66/1.50      | v3_pre_topc(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),sK2)
% 7.66/1.50      | ~ m1_subset_1(k6_subset_1(u1_struct_0(sK2),sK0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_1129]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_673,plain,
% 7.66/1.50      ( X0 != X1 | u1_pre_topc(X0) = u1_pre_topc(X1) ),
% 7.66/1.50      theory(equality) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_684,plain,
% 7.66/1.50      ( u1_pre_topc(sK1) = u1_pre_topc(sK1) | sK1 != sK1 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_673]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_65,plain,
% 7.66/1.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_2,plain,
% 7.66/1.50      ( r1_tarski(X0,X0) ),
% 7.66/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_61,plain,
% 7.66/1.50      ( r1_tarski(sK1,sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_48,plain,
% 7.66/1.50      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 7.66/1.50      | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_7]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(c_38,plain,
% 7.66/1.50      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 7.66/1.50      inference(instantiation,[status(thm)],[c_13]) ).
% 7.66/1.50  
% 7.66/1.50  cnf(contradiction,plain,
% 7.66/1.50      ( $false ),
% 7.66/1.50      inference(minisat,
% 7.66/1.50                [status(thm)],
% 7.66/1.50                [c_21468,c_13660,c_9137,c_5778,c_5666,c_4587,c_4564,
% 7.66/1.50                 c_3889,c_2912,c_2851,c_2812,c_2502,c_2402,c_2176,c_2037,
% 7.66/1.50                 c_1654,c_1431,c_1430,c_1254,c_1253,c_1131,c_684,c_312,
% 7.66/1.50                 c_65,c_61,c_48,c_39,c_38,c_19,c_20,c_25,c_22,c_24,c_23]) ).
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.50  
% 7.66/1.50  ------                               Statistics
% 7.66/1.50  
% 7.66/1.50  ------ General
% 7.66/1.50  
% 7.66/1.50  abstr_ref_over_cycles:                  0
% 7.66/1.50  abstr_ref_under_cycles:                 0
% 7.66/1.50  gc_basic_clause_elim:                   0
% 7.66/1.50  forced_gc_time:                         0
% 7.66/1.50  parsing_time:                           0.029
% 7.66/1.50  unif_index_cands_time:                  0.
% 7.66/1.50  unif_index_add_time:                    0.
% 7.66/1.50  orderings_time:                         0.
% 7.66/1.50  out_proof_time:                         0.014
% 7.66/1.50  total_time:                             0.708
% 7.66/1.50  num_of_symbols:                         46
% 7.66/1.50  num_of_terms:                           8332
% 7.66/1.50  
% 7.66/1.50  ------ Preprocessing
% 7.66/1.50  
% 7.66/1.50  num_of_splits:                          0
% 7.66/1.50  num_of_split_atoms:                     0
% 7.66/1.50  num_of_reused_defs:                     0
% 7.66/1.50  num_eq_ax_congr_red:                    12
% 7.66/1.50  num_of_sem_filtered_clauses:            1
% 7.66/1.50  num_of_subtypes:                        0
% 7.66/1.50  monotx_restored_types:                  0
% 7.66/1.50  sat_num_of_epr_types:                   0
% 7.66/1.50  sat_num_of_non_cyclic_types:            0
% 7.66/1.50  sat_guarded_non_collapsed_types:        0
% 7.66/1.50  num_pure_diseq_elim:                    0
% 7.66/1.50  simp_replaced_by:                       0
% 7.66/1.50  res_preprocessed:                       115
% 7.66/1.50  prep_upred:                             0
% 7.66/1.50  prep_unflattend:                        14
% 7.66/1.50  smt_new_axioms:                         0
% 7.66/1.50  pred_elim_cands:                        7
% 7.66/1.50  pred_elim:                              0
% 7.66/1.50  pred_elim_cl:                           0
% 7.66/1.50  pred_elim_cycles:                       2
% 7.66/1.50  merged_defs:                            0
% 7.66/1.50  merged_defs_ncl:                        0
% 7.66/1.50  bin_hyper_res:                          0
% 7.66/1.50  prep_cycles:                            4
% 7.66/1.50  pred_elim_time:                         0.005
% 7.66/1.50  splitting_time:                         0.
% 7.66/1.50  sem_filter_time:                        0.
% 7.66/1.50  monotx_time:                            0.
% 7.66/1.50  subtype_inf_time:                       0.
% 7.66/1.50  
% 7.66/1.50  ------ Problem properties
% 7.66/1.50  
% 7.66/1.50  clauses:                                22
% 7.66/1.50  conjectures:                            5
% 7.66/1.50  epr:                                    8
% 7.66/1.50  horn:                                   20
% 7.66/1.50  ground:                                 5
% 7.66/1.50  unary:                                  6
% 7.66/1.50  binary:                                 2
% 7.66/1.50  lits:                                   59
% 7.66/1.50  lits_eq:                                2
% 7.66/1.50  fd_pure:                                0
% 7.66/1.50  fd_pseudo:                              0
% 7.66/1.50  fd_cond:                                0
% 7.66/1.50  fd_pseudo_cond:                         1
% 7.66/1.50  ac_symbols:                             0
% 7.66/1.50  
% 7.66/1.50  ------ Propositional Solver
% 7.66/1.50  
% 7.66/1.50  prop_solver_calls:                      38
% 7.66/1.50  prop_fast_solver_calls:                 2536
% 7.66/1.50  smt_solver_calls:                       0
% 7.66/1.50  smt_fast_solver_calls:                  0
% 7.66/1.50  prop_num_of_clauses:                    6149
% 7.66/1.50  prop_preprocess_simplified:             11949
% 7.66/1.50  prop_fo_subsumed:                       196
% 7.66/1.50  prop_solver_time:                       0.
% 7.66/1.50  smt_solver_time:                        0.
% 7.66/1.50  smt_fast_solver_time:                   0.
% 7.66/1.50  prop_fast_solver_time:                  0.
% 7.66/1.50  prop_unsat_core_time:                   0.
% 7.66/1.50  
% 7.66/1.50  ------ QBF
% 7.66/1.50  
% 7.66/1.50  qbf_q_res:                              0
% 7.66/1.50  qbf_num_tautologies:                    0
% 7.66/1.50  qbf_prep_cycles:                        0
% 7.66/1.50  
% 7.66/1.50  ------ BMC1
% 7.66/1.50  
% 7.66/1.50  bmc1_current_bound:                     -1
% 7.66/1.50  bmc1_last_solved_bound:                 -1
% 7.66/1.50  bmc1_unsat_core_size:                   -1
% 7.66/1.50  bmc1_unsat_core_parents_size:           -1
% 7.66/1.50  bmc1_merge_next_fun:                    0
% 7.66/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.50  
% 7.66/1.50  ------ Instantiation
% 7.66/1.50  
% 7.66/1.50  inst_num_of_clauses:                    1599
% 7.66/1.50  inst_num_in_passive:                    147
% 7.66/1.50  inst_num_in_active:                     1146
% 7.66/1.50  inst_num_in_unprocessed:                305
% 7.66/1.50  inst_num_of_loops:                      1217
% 7.66/1.50  inst_num_of_learning_restarts:          0
% 7.66/1.50  inst_num_moves_active_passive:          59
% 7.66/1.50  inst_lit_activity:                      0
% 7.66/1.50  inst_lit_activity_moves:                0
% 7.66/1.50  inst_num_tautologies:                   0
% 7.66/1.50  inst_num_prop_implied:                  0
% 7.66/1.50  inst_num_existing_simplified:           0
% 7.66/1.50  inst_num_eq_res_simplified:             0
% 7.66/1.50  inst_num_child_elim:                    0
% 7.66/1.50  inst_num_of_dismatching_blockings:      2122
% 7.66/1.50  inst_num_of_non_proper_insts:           4820
% 7.66/1.50  inst_num_of_duplicates:                 0
% 7.66/1.50  inst_inst_num_from_inst_to_res:         0
% 7.66/1.50  inst_dismatching_checking_time:         0.
% 7.66/1.50  
% 7.66/1.50  ------ Resolution
% 7.66/1.50  
% 7.66/1.50  res_num_of_clauses:                     0
% 7.66/1.50  res_num_in_passive:                     0
% 7.66/1.50  res_num_in_active:                      0
% 7.66/1.50  res_num_of_loops:                       119
% 7.66/1.50  res_forward_subset_subsumed:            1084
% 7.66/1.50  res_backward_subset_subsumed:           2
% 7.66/1.50  res_forward_subsumed:                   0
% 7.66/1.50  res_backward_subsumed:                  0
% 7.66/1.50  res_forward_subsumption_resolution:     0
% 7.66/1.50  res_backward_subsumption_resolution:    0
% 7.66/1.50  res_clause_to_clause_subsumption:       3630
% 7.66/1.50  res_orphan_elimination:                 0
% 7.66/1.50  res_tautology_del:                      826
% 7.66/1.50  res_num_eq_res_simplified:              0
% 7.66/1.50  res_num_sel_changes:                    0
% 7.66/1.50  res_moves_from_active_to_pass:          0
% 7.66/1.50  
% 7.66/1.50  ------ Superposition
% 7.66/1.50  
% 7.66/1.50  sup_time_total:                         0.
% 7.66/1.50  sup_time_generating:                    0.
% 7.66/1.50  sup_time_sim_full:                      0.
% 7.66/1.50  sup_time_sim_immed:                     0.
% 7.66/1.50  
% 7.66/1.50  sup_num_of_clauses:                     538
% 7.66/1.50  sup_num_in_active:                      232
% 7.66/1.50  sup_num_in_passive:                     306
% 7.66/1.50  sup_num_of_loops:                       242
% 7.66/1.50  sup_fw_superposition:                   632
% 7.66/1.50  sup_bw_superposition:                   577
% 7.66/1.50  sup_immediate_simplified:               476
% 7.66/1.50  sup_given_eliminated:                   0
% 7.66/1.50  comparisons_done:                       0
% 7.66/1.50  comparisons_avoided:                    0
% 7.66/1.50  
% 7.66/1.50  ------ Simplifications
% 7.66/1.50  
% 7.66/1.50  
% 7.66/1.50  sim_fw_subset_subsumed:                 166
% 7.66/1.50  sim_bw_subset_subsumed:                 11
% 7.66/1.50  sim_fw_subsumed:                        255
% 7.66/1.50  sim_bw_subsumed:                        20
% 7.66/1.50  sim_fw_subsumption_res:                 0
% 7.66/1.50  sim_bw_subsumption_res:                 0
% 7.66/1.50  sim_tautology_del:                      83
% 7.66/1.50  sim_eq_tautology_del:                   18
% 7.66/1.50  sim_eq_res_simp:                        0
% 7.66/1.50  sim_fw_demodulated:                     2
% 7.66/1.50  sim_bw_demodulated:                     3
% 7.66/1.50  sim_light_normalised:                   119
% 7.66/1.50  sim_joinable_taut:                      0
% 7.66/1.50  sim_joinable_simp:                      0
% 7.66/1.50  sim_ac_normalised:                      0
% 7.66/1.50  sim_smt_subsumption:                    0
% 7.66/1.50  
%------------------------------------------------------------------------------
