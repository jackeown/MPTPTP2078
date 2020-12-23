%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:56 EST 2020

% Result     : Theorem 7.56s
% Output     : CNFRefutation 7.56s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 307 expanded)
%              Number of clauses        :  106 ( 144 expanded)
%              Number of leaves         :   19 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 (1267 expanded)
%              Number of equality atoms :  107 ( 117 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v5_tops_1(X2,X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v6_tops_1(X2,X0)
                  & v6_tops_1(X1,X0) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v6_tops_1(X2,X0)
                    & v6_tops_1(X1,X0) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v6_tops_1(X2,X0)
          & v6_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v6_tops_1(sK2,X0)
        & v6_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v6_tops_1(X2,X0)
            & v6_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v6_tops_1(X2,X0)
                & v6_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v6_tops_1(X2,sK0)
              & v6_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v6_tops_1(sK2,sK0)
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26,f25])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_550,plain,
    ( ~ v5_tops_1(X0_44,X0_46)
    | v5_tops_1(X1_44,X0_46)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1644,plain,
    ( v5_tops_1(X0_44,sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1_44),sK0)
    | X0_44 != k3_subset_1(u1_struct_0(sK0),X1_44) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_3163,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0_44),sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1_44),sK0)
    | k3_subset_1(u1_struct_0(sK0),X1_44) != k3_subset_1(u1_struct_0(sK0),X0_44) ),
    inference(instantiation,[status(thm)],[c_1644])).

cnf(c_6772,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0_44),sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),X0_44) ),
    inference(instantiation,[status(thm)],[c_3163])).

cnf(c_20529,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
    inference(instantiation,[status(thm)],[c_6772])).

cnf(c_20531,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
    inference(instantiation,[status(thm)],[c_20529])).

cnf(c_1421,plain,
    ( v5_tops_1(X0_44,sK0)
    | ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | X0_44 != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_19646,plain,
    ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_544,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1661,plain,
    ( X0_44 != X1_44
    | X0_44 = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != X1_44 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_3862,plain,
    ( X0_44 = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
    | X0_44 != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_1661])).

cnf(c_6885,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k3_subset_1(u1_struct_0(sK0),X0_44) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
    | k3_subset_1(u1_struct_0(sK0),X0_44) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_3862])).

cnf(c_16464,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_6885])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_138,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_138])).

cnf(c_174,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_139])).

cnf(c_438,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_467,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_174,c_439])).

cnf(c_527,plain,
    ( ~ r1_tarski(X0_44,X0_45)
    | ~ r1_tarski(X1_44,X0_45)
    | k9_subset_1(X0_45,X1_44,k3_subset_1(X0_45,X0_44)) = k7_subset_1(X0_45,X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_467])).

cnf(c_1113,plain,
    ( ~ r1_tarski(X0_44,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0_44)) = k7_subset_1(u1_struct_0(sK0),sK1,X0_44) ),
    inference(instantiation,[status(thm)],[c_527])).

cnf(c_14909,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_546,plain,
    ( X0_44 != X1_44
    | k3_subset_1(X0_45,X0_44) = k3_subset_1(X0_45,X1_44) ),
    theory(equality)).

cnf(c_3164,plain,
    ( X0_44 != X1_44
    | k3_subset_1(u1_struct_0(sK0),X0_44) = k3_subset_1(u1_struct_0(sK0),X1_44) ),
    inference(instantiation,[status(thm)],[c_546])).

cnf(c_6884,plain,
    ( X0_44 != k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | k3_subset_1(u1_struct_0(sK0),X0_44) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_3164])).

cnf(c_14908,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) != k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_6884])).

cnf(c_7151,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_44
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),X0_44) ),
    inference(instantiation,[status(thm)],[c_3164])).

cnf(c_10478,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
    inference(instantiation,[status(thm)],[c_7151])).

cnf(c_10492,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
    inference(instantiation,[status(thm)],[c_10478])).

cnf(c_548,plain,
    ( X0_44 != X1_44
    | X2_44 != X3_44
    | k9_subset_1(X0_45,X0_44,X2_44) = k9_subset_1(X0_45,X1_44,X3_44) ),
    theory(equality)).

cnf(c_1387,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)
    | sK2 != X1_44
    | sK1 != X0_44 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_7444,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | sK2 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | sK1 != X0_44 ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_7449,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | sK2 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_7444])).

cnf(c_1347,plain,
    ( X0_44 != X1_44
    | sK2 != X1_44
    | sK2 = X0_44 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_2826,plain,
    ( X0_44 != sK2
    | sK2 = X0_44
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1347])).

cnf(c_6739,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) != sK2
    | sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2826])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_541,plain,
    ( ~ r1_tarski(X0_44,X0_45)
    | r1_tarski(k3_xboole_0(X0_44,X1_44),X0_45) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1094,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0_44),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_541])).

cnf(c_2922,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1094])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | r1_tarski(X0_44,X0_45) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1123,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0_44,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_2889,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_175,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_139])).

cnf(c_468,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
    inference(bin_hyper_res,[status(thm)],[c_175,c_439])).

cnf(c_526,plain,
    ( ~ r1_tarski(X0_44,X0_45)
    | ~ r1_tarski(X1_44,X0_45)
    | k4_subset_1(X0_45,k3_subset_1(X0_45,X1_44),X0_44) = k3_subset_1(X0_45,k7_subset_1(X0_45,X1_44,X0_44)) ),
    inference(subtyping,[status(esa)],[c_468])).

cnf(c_1112,plain,
    ( ~ r1_tarski(X0_44,u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0_44) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0_44)) ),
    inference(instantiation,[status(thm)],[c_526])).

cnf(c_2661,plain,
    ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_540,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
    | ~ r1_tarski(X0_44,X0_45) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1276,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0_44,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_540])).

cnf(c_2234,plain,
    ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_543,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1632,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_547,plain,
    ( ~ m1_subset_1(X0_44,X0_47)
    | m1_subset_1(X1_44,X0_47)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1126,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | X1_44 != X0_44 ),
    inference(instantiation,[status(thm)],[c_547])).

cnf(c_1341,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_44 ),
    inference(instantiation,[status(thm)],[c_1126])).

cnf(c_1552,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1341])).

cnf(c_10,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ v5_tops_1(X2,X1)
    | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_17,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_256,plain,
    ( ~ v5_tops_1(X0,X1)
    | ~ v5_tops_1(X2,X1)
    | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_257,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ v5_tops_1(X1,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ v5_tops_1(X1,sK0)
    | ~ v5_tops_1(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_257,c_16])).

cnf(c_262,plain,
    ( ~ v5_tops_1(X0,sK0)
    | ~ v5_tops_1(X1,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_261])).

cnf(c_533,plain,
    ( ~ v5_tops_1(X0_44,sK0)
    | ~ v5_tops_1(X1_44,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,X1_44),sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_262])).

cnf(c_989,plain,
    ( ~ v5_tops_1(X0_44,sK0)
    | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_1332,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_989])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_171,plain,
    ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_139])).

cnf(c_536,plain,
    ( m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45))
    | ~ r1_tarski(X0_44,X0_45) ),
    inference(subtyping,[status(esa)],[c_171])).

cnf(c_1096,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_139])).

cnf(c_535,plain,
    ( ~ r1_tarski(X0_44,X0_45)
    | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_172])).

cnf(c_1063,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_535])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_173,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_3,c_139])).

cnf(c_534,plain,
    ( ~ r1_tarski(X0_44,X0_45)
    | k9_subset_1(X0_45,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_173])).

cnf(c_1065,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),X0_44,sK2) = k3_xboole_0(X0_44,sK2) ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1071,plain,
    ( ~ r1_tarski(sK2,u1_struct_0(sK0))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1065])).

cnf(c_1066,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_536])).

cnf(c_1002,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_999,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_539])).

cnf(c_558,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_543])).

cnf(c_13,negated_conjecture,
    ( v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_9,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_289,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_16])).

cnf(c_290,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_363,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_290])).

cnf(c_364,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_12,negated_conjecture,
    ( v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_352,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_290])).

cnf(c_353,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_11,negated_conjecture,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_304,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | v6_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_16])).

cnf(c_305,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | v6_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_342,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_305])).

cnf(c_343,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20531,c_19646,c_16464,c_14909,c_14908,c_10492,c_7449,c_6739,c_2922,c_2889,c_2661,c_2234,c_1632,c_1552,c_1332,c_1096,c_1063,c_1071,c_1066,c_1002,c_999,c_558,c_364,c_353,c_343,c_14,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.56/1.60  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.56/1.60  
% 7.56/1.60  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.56/1.60  
% 7.56/1.60  ------  iProver source info
% 7.56/1.60  
% 7.56/1.60  git: date: 2020-06-30 10:37:57 +0100
% 7.56/1.60  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.56/1.60  git: non_committed_changes: false
% 7.56/1.60  git: last_make_outside_of_git: false
% 7.56/1.60  
% 7.56/1.60  ------ 
% 7.56/1.60  ------ Parsing...
% 7.56/1.60  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.56/1.60  
% 7.56/1.60  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.56/1.60  
% 7.56/1.60  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.56/1.60  
% 7.56/1.60  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.56/1.60  ------ Proving...
% 7.56/1.60  ------ Problem Properties 
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  clauses                                 16
% 7.56/1.60  conjectures                             2
% 7.56/1.60  EPR                                     0
% 7.56/1.60  Horn                                    16
% 7.56/1.60  unary                                   6
% 7.56/1.60  binary                                  7
% 7.56/1.60  lits                                    31
% 7.56/1.60  lits eq                                 6
% 7.56/1.60  fd_pure                                 0
% 7.56/1.60  fd_pseudo                               0
% 7.56/1.60  fd_cond                                 0
% 7.56/1.60  fd_pseudo_cond                          0
% 7.56/1.60  AC symbols                              0
% 7.56/1.60  
% 7.56/1.60  ------ Input Options Time Limit: Unbounded
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  ------ 
% 7.56/1.60  Current options:
% 7.56/1.60  ------ 
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  ------ Proving...
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  % SZS status Theorem for theBenchmark.p
% 7.56/1.60  
% 7.56/1.60  % SZS output start CNFRefutation for theBenchmark.p
% 7.56/1.60  
% 7.56/1.60  fof(f5,axiom,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f16,plain,(
% 7.56/1.60    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f5])).
% 7.56/1.60  
% 7.56/1.60  fof(f33,plain,(
% 7.56/1.60    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f16])).
% 7.56/1.60  
% 7.56/1.60  fof(f7,axiom,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f23,plain,(
% 7.56/1.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.56/1.60    inference(nnf_transformation,[],[f7])).
% 7.56/1.60  
% 7.56/1.60  fof(f36,plain,(
% 7.56/1.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.56/1.60    inference(cnf_transformation,[],[f23])).
% 7.56/1.60  
% 7.56/1.60  fof(f1,axiom,(
% 7.56/1.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f12,plain,(
% 7.56/1.60    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 7.56/1.60    inference(ennf_transformation,[],[f1])).
% 7.56/1.60  
% 7.56/1.60  fof(f29,plain,(
% 7.56/1.60    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 7.56/1.60    inference(cnf_transformation,[],[f12])).
% 7.56/1.60  
% 7.56/1.60  fof(f35,plain,(
% 7.56/1.60    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f23])).
% 7.56/1.60  
% 7.56/1.60  fof(f6,axiom,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f17,plain,(
% 7.56/1.60    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f6])).
% 7.56/1.60  
% 7.56/1.60  fof(f34,plain,(
% 7.56/1.60    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f17])).
% 7.56/1.60  
% 7.56/1.60  fof(f9,axiom,(
% 7.56/1.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v5_tops_1(X2,X0) & v5_tops_1(X1,X0)) => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f19,plain,(
% 7.56/1.60    ! [X0] : (! [X1] : (! [X2] : ((v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f9])).
% 7.56/1.60  
% 7.56/1.60  fof(f20,plain,(
% 7.56/1.60    ! [X0] : (! [X1] : (! [X2] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.56/1.60    inference(flattening,[],[f19])).
% 7.56/1.60  
% 7.56/1.60  fof(f39,plain,(
% 7.56/1.60    ( ! [X2,X0,X1] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.56/1.60    inference(cnf_transformation,[],[f20])).
% 7.56/1.60  
% 7.56/1.60  fof(f10,conjecture,(
% 7.56/1.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f11,negated_conjecture,(
% 7.56/1.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 7.56/1.60    inference(negated_conjecture,[],[f10])).
% 7.56/1.60  
% 7.56/1.60  fof(f21,plain,(
% 7.56/1.60    ? [X0] : (? [X1] : (? [X2] : ((~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v6_tops_1(X2,X0) & v6_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f11])).
% 7.56/1.60  
% 7.56/1.60  fof(f22,plain,(
% 7.56/1.60    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.56/1.60    inference(flattening,[],[f21])).
% 7.56/1.60  
% 7.56/1.60  fof(f27,plain,(
% 7.56/1.60    ( ! [X0,X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0) & v6_tops_1(sK2,X0) & v6_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.56/1.60    introduced(choice_axiom,[])).
% 7.56/1.60  
% 7.56/1.60  fof(f26,plain,(
% 7.56/1.60    ( ! [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.56/1.60    introduced(choice_axiom,[])).
% 7.56/1.60  
% 7.56/1.60  fof(f25,plain,(
% 7.56/1.60    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v6_tops_1(X2,sK0) & v6_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.56/1.60    introduced(choice_axiom,[])).
% 7.56/1.60  
% 7.56/1.60  fof(f28,plain,(
% 7.56/1.60    ((~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v6_tops_1(sK2,sK0) & v6_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.56/1.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f27,f26,f25])).
% 7.56/1.60  
% 7.56/1.60  fof(f40,plain,(
% 7.56/1.60    v2_pre_topc(sK0)),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f41,plain,(
% 7.56/1.60    l1_pre_topc(sK0)),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f2,axiom,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f13,plain,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f2])).
% 7.56/1.60  
% 7.56/1.60  fof(f30,plain,(
% 7.56/1.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f13])).
% 7.56/1.60  
% 7.56/1.60  fof(f3,axiom,(
% 7.56/1.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f14,plain,(
% 7.56/1.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f3])).
% 7.56/1.60  
% 7.56/1.60  fof(f31,plain,(
% 7.56/1.60    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f14])).
% 7.56/1.60  
% 7.56/1.60  fof(f4,axiom,(
% 7.56/1.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f15,plain,(
% 7.56/1.60    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.56/1.60    inference(ennf_transformation,[],[f4])).
% 7.56/1.60  
% 7.56/1.60  fof(f32,plain,(
% 7.56/1.60    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.56/1.60    inference(cnf_transformation,[],[f15])).
% 7.56/1.60  
% 7.56/1.60  fof(f44,plain,(
% 7.56/1.60    v6_tops_1(sK1,sK0)),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f8,axiom,(
% 7.56/1.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.56/1.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.56/1.60  
% 7.56/1.60  fof(f18,plain,(
% 7.56/1.60    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.56/1.60    inference(ennf_transformation,[],[f8])).
% 7.56/1.60  
% 7.56/1.60  fof(f24,plain,(
% 7.56/1.60    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.56/1.60    inference(nnf_transformation,[],[f18])).
% 7.56/1.60  
% 7.56/1.60  fof(f37,plain,(
% 7.56/1.60    ( ! [X0,X1] : (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.56/1.60    inference(cnf_transformation,[],[f24])).
% 7.56/1.60  
% 7.56/1.60  fof(f45,plain,(
% 7.56/1.60    v6_tops_1(sK2,sK0)),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f46,plain,(
% 7.56/1.60    ~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f38,plain,(
% 7.56/1.60    ( ! [X0,X1] : (v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.56/1.60    inference(cnf_transformation,[],[f24])).
% 7.56/1.60  
% 7.56/1.60  fof(f43,plain,(
% 7.56/1.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  fof(f42,plain,(
% 7.56/1.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.56/1.60    inference(cnf_transformation,[],[f28])).
% 7.56/1.60  
% 7.56/1.60  cnf(c_550,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0_44,X0_46)
% 7.56/1.60      | v5_tops_1(X1_44,X0_46)
% 7.56/1.60      | X1_44 != X0_44 ),
% 7.56/1.60      theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1644,plain,
% 7.56/1.60      ( v5_tops_1(X0_44,sK0)
% 7.56/1.60      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1_44),sK0)
% 7.56/1.60      | X0_44 != k3_subset_1(u1_struct_0(sK0),X1_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_550]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_3163,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0_44),sK0)
% 7.56/1.60      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),X1_44),sK0)
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),X1_44) != k3_subset_1(u1_struct_0(sK0),X0_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1644]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_6772,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0_44),sK0)
% 7.56/1.60      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),X0_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_3163]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_20529,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
% 7.56/1.60      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_6772]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_20531,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
% 7.56/1.60      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_20529]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1421,plain,
% 7.56/1.60      ( v5_tops_1(X0_44,sK0)
% 7.56/1.60      | ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
% 7.56/1.60      | X0_44 != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_550]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_19646,plain,
% 7.56/1.60      ( ~ v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
% 7.56/1.60      | v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))),sK0)
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) != k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1421]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_544,plain,
% 7.56/1.60      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 7.56/1.60      theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1661,plain,
% 7.56/1.60      ( X0_44 != X1_44
% 7.56/1.60      | X0_44 = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != X1_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_544]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_3862,plain,
% 7.56/1.60      ( X0_44 = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | X0_44 != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1661]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_6885,plain,
% 7.56/1.60      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),X0_44) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),X0_44) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_3862]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_16464,plain,
% 7.56/1.60      ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) != k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_6885]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_4,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.56/1.60      | k9_subset_1(X1,X0,k3_subset_1(X1,X2)) = k7_subset_1(X1,X0,X2) ),
% 7.56/1.60      inference(cnf_transformation,[],[f33]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_6,plain,
% 7.56/1.60      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.56/1.60      inference(cnf_transformation,[],[f36]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_138,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.56/1.60      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_139,plain,
% 7.56/1.60      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.56/1.60      inference(renaming,[status(thm)],[c_138]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_174,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | ~ r1_tarski(X2,X1)
% 7.56/1.60      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_4,c_139]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_438,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.56/1.60      inference(prop_impl,[status(thm)],[c_6]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_439,plain,
% 7.56/1.60      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.56/1.60      inference(renaming,[status(thm)],[c_438]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_467,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1)
% 7.56/1.60      | ~ r1_tarski(X2,X1)
% 7.56/1.60      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_174,c_439]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_527,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,X0_45)
% 7.56/1.60      | ~ r1_tarski(X1_44,X0_45)
% 7.56/1.60      | k9_subset_1(X0_45,X1_44,k3_subset_1(X0_45,X0_44)) = k7_subset_1(X0_45,X1_44,X0_44) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_467]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1113,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),X0_44)) = k7_subset_1(u1_struct_0(sK0),sK1,X0_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_527]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_14909,plain,
% 7.56/1.60      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1113]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_546,plain,
% 7.56/1.60      ( X0_44 != X1_44
% 7.56/1.60      | k3_subset_1(X0_45,X0_44) = k3_subset_1(X0_45,X1_44) ),
% 7.56/1.60      theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_3164,plain,
% 7.56/1.60      ( X0_44 != X1_44
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),X0_44) = k3_subset_1(u1_struct_0(sK0),X1_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_546]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_6884,plain,
% 7.56/1.60      ( X0_44 != k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),X0_44) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_3164]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_14908,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) != k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_6884]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_7151,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_44
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),X0_44) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_3164]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_10478,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_7151]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_10492,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_10478]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_548,plain,
% 7.56/1.60      ( X0_44 != X1_44
% 7.56/1.60      | X2_44 != X3_44
% 7.56/1.60      | k9_subset_1(X0_45,X0_44,X2_44) = k9_subset_1(X0_45,X1_44,X3_44) ),
% 7.56/1.60      theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1387,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),X0_44,X1_44)
% 7.56/1.60      | sK2 != X1_44
% 7.56/1.60      | sK1 != X0_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_548]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_7444,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | sK2 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | sK1 != X0_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1387]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_7449,plain,
% 7.56/1.60      ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
% 7.56/1.60      | sK2 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | sK1 != sK1 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_7444]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1347,plain,
% 7.56/1.60      ( X0_44 != X1_44 | sK2 != X1_44 | sK2 = X0_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_544]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2826,plain,
% 7.56/1.60      ( X0_44 != sK2 | sK2 = X0_44 | sK2 != sK2 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1347]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_6739,plain,
% 7.56/1.60      ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) != sK2
% 7.56/1.60      | sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
% 7.56/1.60      | sK2 != sK2 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_2826]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_0,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1) ),
% 7.56/1.60      inference(cnf_transformation,[],[f29]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_541,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,X0_45)
% 7.56/1.60      | r1_tarski(k3_xboole_0(X0_44,X1_44),X0_45) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_0]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1094,plain,
% 7.56/1.60      ( r1_tarski(k3_xboole_0(sK1,X0_44),u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_541]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2922,plain,
% 7.56/1.60      ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1094]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_7,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.56/1.60      inference(cnf_transformation,[],[f35]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_539,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 7.56/1.60      | r1_tarski(X0_44,X0_45) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_7]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1123,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | r1_tarski(X0_44,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_539]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2889,plain,
% 7.56/1.60      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1123]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_5,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.56/1.60      | k4_subset_1(X1,k3_subset_1(X1,X0),X2) = k3_subset_1(X1,k7_subset_1(X1,X0,X2)) ),
% 7.56/1.60      inference(cnf_transformation,[],[f34]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_175,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | ~ r1_tarski(X2,X1)
% 7.56/1.60      | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_5,c_139]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_468,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1)
% 7.56/1.60      | ~ r1_tarski(X2,X1)
% 7.56/1.60      | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_175,c_439]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_526,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,X0_45)
% 7.56/1.60      | ~ r1_tarski(X1_44,X0_45)
% 7.56/1.60      | k4_subset_1(X0_45,k3_subset_1(X0_45,X1_44),X0_44) = k3_subset_1(X0_45,k7_subset_1(X0_45,X1_44,X0_44)) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_468]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1112,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 7.56/1.60      | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0_44) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0_44)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_526]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2661,plain,
% 7.56/1.60      ( ~ r1_tarski(k3_subset_1(u1_struct_0(sK0),sK2),u1_struct_0(sK0))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0))
% 7.56/1.60      | k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1112]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_540,plain,
% 7.56/1.60      ( m1_subset_1(X0_44,k1_zfmisc_1(X0_45))
% 7.56/1.60      | ~ r1_tarski(X0_44,X0_45) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_6]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1276,plain,
% 7.56/1.60      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ r1_tarski(X0_44,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_540]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2234,plain,
% 7.56/1.60      ( m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1276]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_543,plain,( X0_44 = X0_44 ),theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1632,plain,
% 7.56/1.60      ( sK2 = sK2 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_543]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_547,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0_44,X0_47)
% 7.56/1.60      | m1_subset_1(X1_44,X0_47)
% 7.56/1.60      | X1_44 != X0_44 ),
% 7.56/1.60      theory(equality) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1126,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | X1_44 != X0_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_547]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1341,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0_44 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1126]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1552,plain,
% 7.56/1.60      ( m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k3_xboole_0(sK1,sK2) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1341]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_10,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0,X1)
% 7.56/1.60      | ~ v5_tops_1(X2,X1)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
% 7.56/1.60      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.56/1.60      | ~ v2_pre_topc(X1)
% 7.56/1.60      | ~ l1_pre_topc(X1) ),
% 7.56/1.60      inference(cnf_transformation,[],[f39]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_17,negated_conjecture,
% 7.56/1.60      ( v2_pre_topc(sK0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f40]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_256,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0,X1)
% 7.56/1.60      | ~ v5_tops_1(X2,X1)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(X1),X2,X0),X1)
% 7.56/1.60      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.56/1.60      | ~ l1_pre_topc(X1)
% 7.56/1.60      | sK0 != X1 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_257,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0,sK0)
% 7.56/1.60      | ~ v5_tops_1(X1,sK0)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ l1_pre_topc(sK0) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_256]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_16,negated_conjecture,
% 7.56/1.60      ( l1_pre_topc(sK0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f41]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_261,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
% 7.56/1.60      | ~ v5_tops_1(X1,sK0)
% 7.56/1.60      | ~ v5_tops_1(X0,sK0) ),
% 7.56/1.60      inference(global_propositional_subsumption,
% 7.56/1.60                [status(thm)],
% 7.56/1.60                [c_257,c_16]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_262,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0,sK0)
% 7.56/1.60      | ~ v5_tops_1(X1,sK0)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0,X1),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(renaming,[status(thm)],[c_261]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_533,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0_44,sK0)
% 7.56/1.60      | ~ v5_tops_1(X1_44,sK0)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,X1_44),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_262]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_989,plain,
% 7.56/1.60      ( ~ v5_tops_1(X0_44,sK0)
% 7.56/1.60      | v5_tops_1(k4_subset_1(u1_struct_0(sK0),X0_44,k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
% 7.56/1.60      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_533]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1332,plain,
% 7.56/1.60      ( v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
% 7.56/1.60      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 7.56/1.60      | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 7.56/1.60      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_989]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.56/1.60      inference(cnf_transformation,[],[f30]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_171,plain,
% 7.56/1.60      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
% 7.56/1.60      | ~ r1_tarski(X1,X0) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_1,c_139]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_536,plain,
% 7.56/1.60      ( m1_subset_1(k3_subset_1(X0_45,X0_44),k1_zfmisc_1(X0_45))
% 7.56/1.60      | ~ r1_tarski(X0_44,X0_45) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_171]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1096,plain,
% 7.56/1.60      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_536]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_2,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.56/1.60      inference(cnf_transformation,[],[f31]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_172,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_2,c_139]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_535,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,X0_45)
% 7.56/1.60      | k3_subset_1(X0_45,k3_subset_1(X0_45,X0_44)) = X0_44 ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_172]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1063,plain,
% 7.56/1.60      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.56/1.60      | k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) = sK2 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_535]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_3,plain,
% 7.56/1.60      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.56/1.60      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f32]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_173,plain,
% 7.56/1.60      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.56/1.60      inference(bin_hyper_res,[status(thm)],[c_3,c_139]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_534,plain,
% 7.56/1.60      ( ~ r1_tarski(X0_44,X0_45)
% 7.56/1.60      | k9_subset_1(X0_45,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
% 7.56/1.60      inference(subtyping,[status(esa)],[c_173]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1065,plain,
% 7.56/1.60      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),X0_44,sK2) = k3_xboole_0(X0_44,sK2) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_534]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1071,plain,
% 7.56/1.60      ( ~ r1_tarski(sK2,u1_struct_0(sK0))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k3_xboole_0(sK1,sK2) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_1065]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1066,plain,
% 7.56/1.60      ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | ~ r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_536]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_1002,plain,
% 7.56/1.60      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_539]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_999,plain,
% 7.56/1.60      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | r1_tarski(sK2,u1_struct_0(sK0)) ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_539]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_558,plain,
% 7.56/1.60      ( sK1 = sK1 ),
% 7.56/1.60      inference(instantiation,[status(thm)],[c_543]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_13,negated_conjecture,
% 7.56/1.60      ( v6_tops_1(sK1,sK0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f44]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_9,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.56/1.60      | ~ v6_tops_1(X1,X0)
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.56/1.60      | ~ l1_pre_topc(X0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f37]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_289,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.56/1.60      | ~ v6_tops_1(X1,X0)
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.56/1.60      | sK0 != X0 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_9,c_16]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_290,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.56/1.60      | ~ v6_tops_1(X0,sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_289]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_363,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | sK1 != X0
% 7.56/1.60      | sK0 != sK0 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_13,c_290]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_364,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
% 7.56/1.60      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_363]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_12,negated_conjecture,
% 7.56/1.60      ( v6_tops_1(sK2,sK0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f45]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_352,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | sK2 != X0
% 7.56/1.60      | sK0 != sK0 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_12,c_290]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_353,plain,
% 7.56/1.60      ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 7.56/1.60      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_352]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_11,negated_conjecture,
% 7.56/1.60      ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f46]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_8,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.56/1.60      | v6_tops_1(X1,X0)
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.56/1.60      | ~ l1_pre_topc(X0) ),
% 7.56/1.60      inference(cnf_transformation,[],[f38]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_304,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.56/1.60      | v6_tops_1(X1,X0)
% 7.56/1.60      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.56/1.60      | sK0 != X0 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_8,c_16]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_305,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.56/1.60      | v6_tops_1(X0,sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_304]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_342,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 7.56/1.60      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.56/1.60      | k9_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 7.56/1.60      | sK0 != sK0 ),
% 7.56/1.60      inference(resolution_lifted,[status(thm)],[c_11,c_305]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_343,plain,
% 7.56/1.60      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
% 7.56/1.60      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(unflattening,[status(thm)],[c_342]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_14,negated_conjecture,
% 7.56/1.60      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(cnf_transformation,[],[f43]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(c_15,negated_conjecture,
% 7.56/1.60      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.56/1.60      inference(cnf_transformation,[],[f42]) ).
% 7.56/1.60  
% 7.56/1.60  cnf(contradiction,plain,
% 7.56/1.60      ( $false ),
% 7.56/1.60      inference(minisat,
% 7.56/1.60                [status(thm)],
% 7.56/1.60                [c_20531,c_19646,c_16464,c_14909,c_14908,c_10492,c_7449,
% 7.56/1.60                 c_6739,c_2922,c_2889,c_2661,c_2234,c_1632,c_1552,c_1332,
% 7.56/1.60                 c_1096,c_1063,c_1071,c_1066,c_1002,c_999,c_558,c_364,
% 7.56/1.60                 c_353,c_343,c_14,c_15]) ).
% 7.56/1.60  
% 7.56/1.60  
% 7.56/1.60  % SZS output end CNFRefutation for theBenchmark.p
% 7.56/1.60  
% 7.56/1.60  ------                               Statistics
% 7.56/1.60  
% 7.56/1.60  ------ Selected
% 7.56/1.60  
% 7.56/1.60  total_time:                             0.746
% 7.56/1.60  
%------------------------------------------------------------------------------
