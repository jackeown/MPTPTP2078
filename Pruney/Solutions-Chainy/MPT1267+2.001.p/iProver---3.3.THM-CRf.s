%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:01 EST 2020

% Result     : Theorem 23.50s
% Output     : CNFRefutation 23.50s
% Verified   : 
% Statistics : Number of formulae       :  234 (3399 expanded)
%              Number of clauses        :  149 (1094 expanded)
%              Number of leaves         :   26 ( 935 expanded)
%              Depth                    :   28
%              Number of atoms          :  608 (16817 expanded)
%              Number of equality atoms :  236 (1507 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v2_tops_1(X2,X0)
                    & v2_tops_1(X1,X0) )
                 => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v4_pre_topc(X2,X0)
          & v2_tops_1(X2,X0)
          & v2_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v4_pre_topc(sK2,X0)
        & v2_tops_1(sK2,X0)
        & v2_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v4_pre_topc(X2,X0)
            & v2_tops_1(X2,X0)
            & v2_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v2_tops_1(X2,X0)
                & v2_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v2_tops_1(X2,sK0)
              & v2_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v2_tops_1(sK2,sK0)
    & v2_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f62,f70,f69,f68])).

fof(f108,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f91,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f90,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f39])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f109,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f105,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f100,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f111,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f110,plain,(
    v2_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f112,plain,(
    ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f104,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1710,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_19,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_447,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_19,c_18])).

cnf(c_39,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_571,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_447,c_39])).

cnf(c_572,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_571])).

cnf(c_1725,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1710,c_572])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1719,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4293,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_1725,c_1719])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1718,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5266,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4293,c_1718])).

cnf(c_23466,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5266,c_1725])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1709,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1724,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1709,c_572])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_695,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_695])).

cnf(c_1705,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_1732,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1705,c_572])).

cnf(c_2570,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),X0,X1)))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1717,c_1732])).

cnf(c_7086,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,X0)))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_2570])).

cnf(c_9363,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),X0))))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),X0)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_7086])).

cnf(c_79030,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)))))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)))) ),
    inference(superposition,[status(thm)],[c_23466,c_9363])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1716,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4280,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_1725,c_1716])).

cnf(c_5191,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4280,c_4280,c_4293])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1715,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6585,plain,
    ( k4_subset_1(k2_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1715])).

cnf(c_6855,plain,
    ( k4_subset_1(k2_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1724,c_6585])).

cnf(c_4292,plain,
    ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
    inference(superposition,[status(thm)],[c_1724,c_1719])).

cnf(c_5247,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4292,c_1718])).

cnf(c_23220,plain,
    ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5247,c_1724])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1720,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_23230,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    inference(superposition,[status(thm)],[c_23220,c_1720])).

cnf(c_36,negated_conjecture,
    ( v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_30,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_40,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_480,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ v1_tops_1(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_40])).

cnf(c_481,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v1_tops_1(X1,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_485,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(X1,sK0)
    | ~ v3_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_39])).

cnf(c_486,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ v1_tops_1(X1,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
    inference(renaming,[status(thm)],[c_485])).

cnf(c_29,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_34,negated_conjecture,
    ( v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_535,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_34])).

cnf(c_536,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_538,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_39,c_37])).

cnf(c_548,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)) = k2_pre_topc(sK0,X1)
    | k3_subset_1(u1_struct_0(sK0),sK2) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_486,c_538])).

cnf(c_549,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),X0)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_25,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_635,plain,
    ( ~ v2_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_39])).

cnf(c_636,plain,
    ( ~ v2_tops_1(X0,sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_635])).

cnf(c_801,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),X1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_549,c_636])).

cnf(c_802,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_816,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_802,c_8])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_816])).

cnf(c_971,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(unflattening,[status(thm)],[c_970])).

cnf(c_973,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_971,c_38])).

cnf(c_1696,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_973])).

cnf(c_35,negated_conjecture,
    ( v2_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_23,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_665,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_39])).

cnf(c_666,plain,
    ( ~ v1_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_665])).

cnf(c_781,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X1) = k2_struct_0(sK0)
    | k3_subset_1(u1_struct_0(sK0),X0) != X1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_666,c_636])).

cnf(c_782,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_781])).

cnf(c_794,plain,
    ( ~ v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_782,c_8])).

cnf(c_954,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_794])).

cnf(c_955,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_957,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_37])).

cnf(c_1729,plain,
    ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_957,c_572])).

cnf(c_1737,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0)
    | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1696,c_572,c_1729])).

cnf(c_4130,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1718,c_1737])).

cnf(c_8420,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4130,c_1725])).

cnf(c_8422,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_8420,c_4292,c_4293])).

cnf(c_30929,plain,
    ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2))) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_23230,c_8422])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1713,plain,
    ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8328,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1713])).

cnf(c_8329,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),X0,sK2)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8328,c_4293])).

cnf(c_27768,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) ),
    inference(superposition,[status(thm)],[c_23220,c_8329])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1714,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_23231,plain,
    ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),X0) ),
    inference(superposition,[status(thm)],[c_23220,c_1714])).

cnf(c_2,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_23266,plain,
    ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,X0)) ),
    inference(demodulation,[status(thm)],[c_23231,c_2])).

cnf(c_27775,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_27768,c_23266])).

cnf(c_30930,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_30929,c_27775])).

cnf(c_6584,plain,
    ( k4_subset_1(k2_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_1715])).

cnf(c_6727,plain,
    ( k4_subset_1(k2_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1725,c_6584])).

cnf(c_6848,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6727,c_1717])).

cnf(c_40093,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6848,c_1724,c_1725])).

cnf(c_40111,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_40093,c_1719])).

cnf(c_23476,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) ),
    inference(superposition,[status(thm)],[c_23466,c_1720])).

cnf(c_8327,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1724,c_1713])).

cnf(c_8330,plain,
    ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8327,c_4292])).

cnf(c_30641,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),sK1) ),
    inference(superposition,[status(thm)],[c_23466,c_8330])).

cnf(c_23477,plain,
    ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK2),X0) ),
    inference(superposition,[status(thm)],[c_23466,c_1714])).

cnf(c_23512,plain,
    ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,X0)) ),
    inference(demodulation,[status(thm)],[c_23477,c_2])).

cnf(c_30650,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(demodulation,[status(thm)],[c_30641,c_23512])).

cnf(c_33767,plain,
    ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_23476,c_30650])).

cnf(c_33771,plain,
    ( k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_33767,c_27775])).

cnf(c_40166,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_40111,c_33771])).

cnf(c_40112,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1))) = k2_xboole_0(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_40093,c_1716])).

cnf(c_40169,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_40166,c_40112])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1712,plain,
    ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8403,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0),sK2) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),X0,sK2))
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_1712])).

cnf(c_23242,plain,
    ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK2) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2)) ),
    inference(superposition,[status(thm)],[c_23220,c_8403])).

cnf(c_4279,plain,
    ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1724,c_1716])).

cnf(c_5184,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4279,c_4279,c_4292])).

cnf(c_23259,plain,
    ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2)) = k2_xboole_0(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_23242,c_5184,c_6855])).

cnf(c_23267,plain,
    ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_23266,c_23259])).

cnf(c_40174,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_40169,c_23267])).

cnf(c_40503,plain,
    ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
    inference(light_normalisation,[status(thm)],[c_40111,c_33771,c_40174])).

cnf(c_79048,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_79030,c_5191,c_6855,c_30930,c_40503])).

cnf(c_17,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1711,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4278,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1711,c_1716])).

cnf(c_4291,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1711,c_1719])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1723,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1721,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2744,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_1723,c_1721])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2745,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2744,c_0])).

cnf(c_4294,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4291,c_2745])).

cnf(c_9133,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4278,c_4278,c_4294])).

cnf(c_79049,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_79048,c_9133])).

cnf(c_6900,plain,
    ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6855,c_1717])).

cnf(c_33,negated_conjecture,
    ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_31,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_608,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_39])).

cnf(c_609,plain,
    ( v2_tops_1(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_930,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
    | k1_tops_1(sK0,X0) != k1_xboole_0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_609])).

cnf(c_931,plain,
    ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_930])).

cnf(c_1698,plain,
    ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_xboole_0
    | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_1733,plain,
    ( k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,sK2)) != k1_xboole_0
    | m1_subset_1(k4_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1698,c_572])).

cnf(c_6894,plain,
    ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_xboole_0
    | m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6855,c_1733])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79049,c_6900,c_6894,c_1725,c_1724])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:05:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 23.50/3.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.50/3.50  
% 23.50/3.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.50/3.50  
% 23.50/3.50  ------  iProver source info
% 23.50/3.50  
% 23.50/3.50  git: date: 2020-06-30 10:37:57 +0100
% 23.50/3.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.50/3.50  git: non_committed_changes: false
% 23.50/3.50  git: last_make_outside_of_git: false
% 23.50/3.50  
% 23.50/3.50  ------ 
% 23.50/3.50  
% 23.50/3.50  ------ Input Options
% 23.50/3.50  
% 23.50/3.50  --out_options                           all
% 23.50/3.50  --tptp_safe_out                         true
% 23.50/3.50  --problem_path                          ""
% 23.50/3.50  --include_path                          ""
% 23.50/3.50  --clausifier                            res/vclausify_rel
% 23.50/3.50  --clausifier_options                    ""
% 23.50/3.50  --stdin                                 false
% 23.50/3.50  --stats_out                             all
% 23.50/3.50  
% 23.50/3.50  ------ General Options
% 23.50/3.50  
% 23.50/3.50  --fof                                   false
% 23.50/3.50  --time_out_real                         305.
% 23.50/3.50  --time_out_virtual                      -1.
% 23.50/3.50  --symbol_type_check                     false
% 23.50/3.50  --clausify_out                          false
% 23.50/3.50  --sig_cnt_out                           false
% 23.50/3.50  --trig_cnt_out                          false
% 23.50/3.50  --trig_cnt_out_tolerance                1.
% 23.50/3.50  --trig_cnt_out_sk_spl                   false
% 23.50/3.50  --abstr_cl_out                          false
% 23.50/3.50  
% 23.50/3.50  ------ Global Options
% 23.50/3.50  
% 23.50/3.50  --schedule                              default
% 23.50/3.50  --add_important_lit                     false
% 23.50/3.50  --prop_solver_per_cl                    1000
% 23.50/3.50  --min_unsat_core                        false
% 23.50/3.50  --soft_assumptions                      false
% 23.50/3.50  --soft_lemma_size                       3
% 23.50/3.50  --prop_impl_unit_size                   0
% 23.50/3.50  --prop_impl_unit                        []
% 23.50/3.50  --share_sel_clauses                     true
% 23.50/3.50  --reset_solvers                         false
% 23.50/3.50  --bc_imp_inh                            [conj_cone]
% 23.50/3.50  --conj_cone_tolerance                   3.
% 23.50/3.50  --extra_neg_conj                        none
% 23.50/3.50  --large_theory_mode                     true
% 23.50/3.50  --prolific_symb_bound                   200
% 23.50/3.50  --lt_threshold                          2000
% 23.50/3.50  --clause_weak_htbl                      true
% 23.50/3.50  --gc_record_bc_elim                     false
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing Options
% 23.50/3.50  
% 23.50/3.50  --preprocessing_flag                    true
% 23.50/3.50  --time_out_prep_mult                    0.1
% 23.50/3.50  --splitting_mode                        input
% 23.50/3.50  --splitting_grd                         true
% 23.50/3.50  --splitting_cvd                         false
% 23.50/3.50  --splitting_cvd_svl                     false
% 23.50/3.50  --splitting_nvd                         32
% 23.50/3.50  --sub_typing                            true
% 23.50/3.50  --prep_gs_sim                           true
% 23.50/3.50  --prep_unflatten                        true
% 23.50/3.50  --prep_res_sim                          true
% 23.50/3.50  --prep_upred                            true
% 23.50/3.50  --prep_sem_filter                       exhaustive
% 23.50/3.50  --prep_sem_filter_out                   false
% 23.50/3.50  --pred_elim                             true
% 23.50/3.50  --res_sim_input                         true
% 23.50/3.50  --eq_ax_congr_red                       true
% 23.50/3.50  --pure_diseq_elim                       true
% 23.50/3.50  --brand_transform                       false
% 23.50/3.50  --non_eq_to_eq                          false
% 23.50/3.50  --prep_def_merge                        true
% 23.50/3.50  --prep_def_merge_prop_impl              false
% 23.50/3.50  --prep_def_merge_mbd                    true
% 23.50/3.50  --prep_def_merge_tr_red                 false
% 23.50/3.50  --prep_def_merge_tr_cl                  false
% 23.50/3.50  --smt_preprocessing                     true
% 23.50/3.50  --smt_ac_axioms                         fast
% 23.50/3.50  --preprocessed_out                      false
% 23.50/3.50  --preprocessed_stats                    false
% 23.50/3.50  
% 23.50/3.50  ------ Abstraction refinement Options
% 23.50/3.50  
% 23.50/3.50  --abstr_ref                             []
% 23.50/3.50  --abstr_ref_prep                        false
% 23.50/3.50  --abstr_ref_until_sat                   false
% 23.50/3.50  --abstr_ref_sig_restrict                funpre
% 23.50/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.50/3.50  --abstr_ref_under                       []
% 23.50/3.50  
% 23.50/3.50  ------ SAT Options
% 23.50/3.50  
% 23.50/3.50  --sat_mode                              false
% 23.50/3.50  --sat_fm_restart_options                ""
% 23.50/3.50  --sat_gr_def                            false
% 23.50/3.50  --sat_epr_types                         true
% 23.50/3.50  --sat_non_cyclic_types                  false
% 23.50/3.50  --sat_finite_models                     false
% 23.50/3.50  --sat_fm_lemmas                         false
% 23.50/3.50  --sat_fm_prep                           false
% 23.50/3.50  --sat_fm_uc_incr                        true
% 23.50/3.50  --sat_out_model                         small
% 23.50/3.50  --sat_out_clauses                       false
% 23.50/3.50  
% 23.50/3.50  ------ QBF Options
% 23.50/3.50  
% 23.50/3.50  --qbf_mode                              false
% 23.50/3.50  --qbf_elim_univ                         false
% 23.50/3.50  --qbf_dom_inst                          none
% 23.50/3.50  --qbf_dom_pre_inst                      false
% 23.50/3.50  --qbf_sk_in                             false
% 23.50/3.50  --qbf_pred_elim                         true
% 23.50/3.50  --qbf_split                             512
% 23.50/3.50  
% 23.50/3.50  ------ BMC1 Options
% 23.50/3.50  
% 23.50/3.50  --bmc1_incremental                      false
% 23.50/3.50  --bmc1_axioms                           reachable_all
% 23.50/3.50  --bmc1_min_bound                        0
% 23.50/3.50  --bmc1_max_bound                        -1
% 23.50/3.50  --bmc1_max_bound_default                -1
% 23.50/3.50  --bmc1_symbol_reachability              true
% 23.50/3.50  --bmc1_property_lemmas                  false
% 23.50/3.50  --bmc1_k_induction                      false
% 23.50/3.50  --bmc1_non_equiv_states                 false
% 23.50/3.50  --bmc1_deadlock                         false
% 23.50/3.50  --bmc1_ucm                              false
% 23.50/3.50  --bmc1_add_unsat_core                   none
% 23.50/3.50  --bmc1_unsat_core_children              false
% 23.50/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.50/3.50  --bmc1_out_stat                         full
% 23.50/3.50  --bmc1_ground_init                      false
% 23.50/3.50  --bmc1_pre_inst_next_state              false
% 23.50/3.50  --bmc1_pre_inst_state                   false
% 23.50/3.50  --bmc1_pre_inst_reach_state             false
% 23.50/3.50  --bmc1_out_unsat_core                   false
% 23.50/3.50  --bmc1_aig_witness_out                  false
% 23.50/3.50  --bmc1_verbose                          false
% 23.50/3.50  --bmc1_dump_clauses_tptp                false
% 23.50/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.50/3.50  --bmc1_dump_file                        -
% 23.50/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.50/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.50/3.50  --bmc1_ucm_extend_mode                  1
% 23.50/3.50  --bmc1_ucm_init_mode                    2
% 23.50/3.50  --bmc1_ucm_cone_mode                    none
% 23.50/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.50/3.50  --bmc1_ucm_relax_model                  4
% 23.50/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.50/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.50/3.50  --bmc1_ucm_layered_model                none
% 23.50/3.50  --bmc1_ucm_max_lemma_size               10
% 23.50/3.50  
% 23.50/3.50  ------ AIG Options
% 23.50/3.50  
% 23.50/3.50  --aig_mode                              false
% 23.50/3.50  
% 23.50/3.50  ------ Instantiation Options
% 23.50/3.50  
% 23.50/3.50  --instantiation_flag                    true
% 23.50/3.50  --inst_sos_flag                         true
% 23.50/3.50  --inst_sos_phase                        true
% 23.50/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.50/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.50/3.50  --inst_lit_sel_side                     num_symb
% 23.50/3.50  --inst_solver_per_active                1400
% 23.50/3.50  --inst_solver_calls_frac                1.
% 23.50/3.50  --inst_passive_queue_type               priority_queues
% 23.50/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.50/3.50  --inst_passive_queues_freq              [25;2]
% 23.50/3.50  --inst_dismatching                      true
% 23.50/3.50  --inst_eager_unprocessed_to_passive     true
% 23.50/3.50  --inst_prop_sim_given                   true
% 23.50/3.50  --inst_prop_sim_new                     false
% 23.50/3.50  --inst_subs_new                         false
% 23.50/3.50  --inst_eq_res_simp                      false
% 23.50/3.50  --inst_subs_given                       false
% 23.50/3.50  --inst_orphan_elimination               true
% 23.50/3.50  --inst_learning_loop_flag               true
% 23.50/3.50  --inst_learning_start                   3000
% 23.50/3.50  --inst_learning_factor                  2
% 23.50/3.50  --inst_start_prop_sim_after_learn       3
% 23.50/3.50  --inst_sel_renew                        solver
% 23.50/3.50  --inst_lit_activity_flag                true
% 23.50/3.50  --inst_restr_to_given                   false
% 23.50/3.50  --inst_activity_threshold               500
% 23.50/3.50  --inst_out_proof                        true
% 23.50/3.50  
% 23.50/3.50  ------ Resolution Options
% 23.50/3.50  
% 23.50/3.50  --resolution_flag                       true
% 23.50/3.50  --res_lit_sel                           adaptive
% 23.50/3.50  --res_lit_sel_side                      none
% 23.50/3.50  --res_ordering                          kbo
% 23.50/3.50  --res_to_prop_solver                    active
% 23.50/3.50  --res_prop_simpl_new                    false
% 23.50/3.50  --res_prop_simpl_given                  true
% 23.50/3.50  --res_passive_queue_type                priority_queues
% 23.50/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.50/3.50  --res_passive_queues_freq               [15;5]
% 23.50/3.50  --res_forward_subs                      full
% 23.50/3.50  --res_backward_subs                     full
% 23.50/3.50  --res_forward_subs_resolution           true
% 23.50/3.50  --res_backward_subs_resolution          true
% 23.50/3.50  --res_orphan_elimination                true
% 23.50/3.50  --res_time_limit                        2.
% 23.50/3.50  --res_out_proof                         true
% 23.50/3.50  
% 23.50/3.50  ------ Superposition Options
% 23.50/3.50  
% 23.50/3.50  --superposition_flag                    true
% 23.50/3.50  --sup_passive_queue_type                priority_queues
% 23.50/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.50/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.50/3.50  --demod_completeness_check              fast
% 23.50/3.50  --demod_use_ground                      true
% 23.50/3.50  --sup_to_prop_solver                    passive
% 23.50/3.50  --sup_prop_simpl_new                    true
% 23.50/3.50  --sup_prop_simpl_given                  true
% 23.50/3.50  --sup_fun_splitting                     true
% 23.50/3.50  --sup_smt_interval                      50000
% 23.50/3.50  
% 23.50/3.50  ------ Superposition Simplification Setup
% 23.50/3.50  
% 23.50/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.50/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.50/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.50/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.50/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.50/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.50/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.50/3.50  --sup_immed_triv                        [TrivRules]
% 23.50/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_immed_bw_main                     []
% 23.50/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.50/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.50/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_input_bw                          []
% 23.50/3.50  
% 23.50/3.50  ------ Combination Options
% 23.50/3.50  
% 23.50/3.50  --comb_res_mult                         3
% 23.50/3.50  --comb_sup_mult                         2
% 23.50/3.50  --comb_inst_mult                        10
% 23.50/3.50  
% 23.50/3.50  ------ Debug Options
% 23.50/3.50  
% 23.50/3.50  --dbg_backtrace                         false
% 23.50/3.50  --dbg_dump_prop_clauses                 false
% 23.50/3.50  --dbg_dump_prop_clauses_file            -
% 23.50/3.50  --dbg_out_stat                          false
% 23.50/3.50  ------ Parsing...
% 23.50/3.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.50/3.50  ------ Proving...
% 23.50/3.50  ------ Problem Properties 
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  clauses                                 38
% 23.50/3.50  conjectures                             2
% 23.50/3.50  EPR                                     1
% 23.50/3.50  Horn                                    38
% 23.50/3.50  unary                                   14
% 23.50/3.50  binary                                  14
% 23.50/3.50  lits                                    76
% 23.50/3.50  lits eq                                 37
% 23.50/3.50  fd_pure                                 0
% 23.50/3.50  fd_pseudo                               0
% 23.50/3.50  fd_cond                                 0
% 23.50/3.50  fd_pseudo_cond                          1
% 23.50/3.50  AC symbols                              0
% 23.50/3.50  
% 23.50/3.50  ------ Schedule dynamic 5 is on 
% 23.50/3.50  
% 23.50/3.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  ------ 
% 23.50/3.50  Current options:
% 23.50/3.50  ------ 
% 23.50/3.50  
% 23.50/3.50  ------ Input Options
% 23.50/3.50  
% 23.50/3.50  --out_options                           all
% 23.50/3.50  --tptp_safe_out                         true
% 23.50/3.50  --problem_path                          ""
% 23.50/3.50  --include_path                          ""
% 23.50/3.50  --clausifier                            res/vclausify_rel
% 23.50/3.50  --clausifier_options                    ""
% 23.50/3.50  --stdin                                 false
% 23.50/3.50  --stats_out                             all
% 23.50/3.50  
% 23.50/3.50  ------ General Options
% 23.50/3.50  
% 23.50/3.50  --fof                                   false
% 23.50/3.50  --time_out_real                         305.
% 23.50/3.50  --time_out_virtual                      -1.
% 23.50/3.50  --symbol_type_check                     false
% 23.50/3.50  --clausify_out                          false
% 23.50/3.50  --sig_cnt_out                           false
% 23.50/3.50  --trig_cnt_out                          false
% 23.50/3.50  --trig_cnt_out_tolerance                1.
% 23.50/3.50  --trig_cnt_out_sk_spl                   false
% 23.50/3.50  --abstr_cl_out                          false
% 23.50/3.50  
% 23.50/3.50  ------ Global Options
% 23.50/3.50  
% 23.50/3.50  --schedule                              default
% 23.50/3.50  --add_important_lit                     false
% 23.50/3.50  --prop_solver_per_cl                    1000
% 23.50/3.50  --min_unsat_core                        false
% 23.50/3.50  --soft_assumptions                      false
% 23.50/3.50  --soft_lemma_size                       3
% 23.50/3.50  --prop_impl_unit_size                   0
% 23.50/3.50  --prop_impl_unit                        []
% 23.50/3.50  --share_sel_clauses                     true
% 23.50/3.50  --reset_solvers                         false
% 23.50/3.50  --bc_imp_inh                            [conj_cone]
% 23.50/3.50  --conj_cone_tolerance                   3.
% 23.50/3.50  --extra_neg_conj                        none
% 23.50/3.50  --large_theory_mode                     true
% 23.50/3.50  --prolific_symb_bound                   200
% 23.50/3.50  --lt_threshold                          2000
% 23.50/3.50  --clause_weak_htbl                      true
% 23.50/3.50  --gc_record_bc_elim                     false
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing Options
% 23.50/3.50  
% 23.50/3.50  --preprocessing_flag                    true
% 23.50/3.50  --time_out_prep_mult                    0.1
% 23.50/3.50  --splitting_mode                        input
% 23.50/3.50  --splitting_grd                         true
% 23.50/3.50  --splitting_cvd                         false
% 23.50/3.50  --splitting_cvd_svl                     false
% 23.50/3.50  --splitting_nvd                         32
% 23.50/3.50  --sub_typing                            true
% 23.50/3.50  --prep_gs_sim                           true
% 23.50/3.50  --prep_unflatten                        true
% 23.50/3.50  --prep_res_sim                          true
% 23.50/3.50  --prep_upred                            true
% 23.50/3.50  --prep_sem_filter                       exhaustive
% 23.50/3.50  --prep_sem_filter_out                   false
% 23.50/3.50  --pred_elim                             true
% 23.50/3.50  --res_sim_input                         true
% 23.50/3.50  --eq_ax_congr_red                       true
% 23.50/3.50  --pure_diseq_elim                       true
% 23.50/3.50  --brand_transform                       false
% 23.50/3.50  --non_eq_to_eq                          false
% 23.50/3.50  --prep_def_merge                        true
% 23.50/3.50  --prep_def_merge_prop_impl              false
% 23.50/3.50  --prep_def_merge_mbd                    true
% 23.50/3.50  --prep_def_merge_tr_red                 false
% 23.50/3.50  --prep_def_merge_tr_cl                  false
% 23.50/3.50  --smt_preprocessing                     true
% 23.50/3.50  --smt_ac_axioms                         fast
% 23.50/3.50  --preprocessed_out                      false
% 23.50/3.50  --preprocessed_stats                    false
% 23.50/3.50  
% 23.50/3.50  ------ Abstraction refinement Options
% 23.50/3.50  
% 23.50/3.50  --abstr_ref                             []
% 23.50/3.50  --abstr_ref_prep                        false
% 23.50/3.50  --abstr_ref_until_sat                   false
% 23.50/3.50  --abstr_ref_sig_restrict                funpre
% 23.50/3.50  --abstr_ref_af_restrict_to_split_sk     false
% 23.50/3.50  --abstr_ref_under                       []
% 23.50/3.50  
% 23.50/3.50  ------ SAT Options
% 23.50/3.50  
% 23.50/3.50  --sat_mode                              false
% 23.50/3.50  --sat_fm_restart_options                ""
% 23.50/3.50  --sat_gr_def                            false
% 23.50/3.50  --sat_epr_types                         true
% 23.50/3.50  --sat_non_cyclic_types                  false
% 23.50/3.50  --sat_finite_models                     false
% 23.50/3.50  --sat_fm_lemmas                         false
% 23.50/3.50  --sat_fm_prep                           false
% 23.50/3.50  --sat_fm_uc_incr                        true
% 23.50/3.50  --sat_out_model                         small
% 23.50/3.50  --sat_out_clauses                       false
% 23.50/3.50  
% 23.50/3.50  ------ QBF Options
% 23.50/3.50  
% 23.50/3.50  --qbf_mode                              false
% 23.50/3.50  --qbf_elim_univ                         false
% 23.50/3.50  --qbf_dom_inst                          none
% 23.50/3.50  --qbf_dom_pre_inst                      false
% 23.50/3.50  --qbf_sk_in                             false
% 23.50/3.50  --qbf_pred_elim                         true
% 23.50/3.50  --qbf_split                             512
% 23.50/3.50  
% 23.50/3.50  ------ BMC1 Options
% 23.50/3.50  
% 23.50/3.50  --bmc1_incremental                      false
% 23.50/3.50  --bmc1_axioms                           reachable_all
% 23.50/3.50  --bmc1_min_bound                        0
% 23.50/3.50  --bmc1_max_bound                        -1
% 23.50/3.50  --bmc1_max_bound_default                -1
% 23.50/3.50  --bmc1_symbol_reachability              true
% 23.50/3.50  --bmc1_property_lemmas                  false
% 23.50/3.50  --bmc1_k_induction                      false
% 23.50/3.50  --bmc1_non_equiv_states                 false
% 23.50/3.50  --bmc1_deadlock                         false
% 23.50/3.50  --bmc1_ucm                              false
% 23.50/3.50  --bmc1_add_unsat_core                   none
% 23.50/3.50  --bmc1_unsat_core_children              false
% 23.50/3.50  --bmc1_unsat_core_extrapolate_axioms    false
% 23.50/3.50  --bmc1_out_stat                         full
% 23.50/3.50  --bmc1_ground_init                      false
% 23.50/3.50  --bmc1_pre_inst_next_state              false
% 23.50/3.50  --bmc1_pre_inst_state                   false
% 23.50/3.50  --bmc1_pre_inst_reach_state             false
% 23.50/3.50  --bmc1_out_unsat_core                   false
% 23.50/3.50  --bmc1_aig_witness_out                  false
% 23.50/3.50  --bmc1_verbose                          false
% 23.50/3.50  --bmc1_dump_clauses_tptp                false
% 23.50/3.50  --bmc1_dump_unsat_core_tptp             false
% 23.50/3.50  --bmc1_dump_file                        -
% 23.50/3.50  --bmc1_ucm_expand_uc_limit              128
% 23.50/3.50  --bmc1_ucm_n_expand_iterations          6
% 23.50/3.50  --bmc1_ucm_extend_mode                  1
% 23.50/3.50  --bmc1_ucm_init_mode                    2
% 23.50/3.50  --bmc1_ucm_cone_mode                    none
% 23.50/3.50  --bmc1_ucm_reduced_relation_type        0
% 23.50/3.50  --bmc1_ucm_relax_model                  4
% 23.50/3.50  --bmc1_ucm_full_tr_after_sat            true
% 23.50/3.50  --bmc1_ucm_expand_neg_assumptions       false
% 23.50/3.50  --bmc1_ucm_layered_model                none
% 23.50/3.50  --bmc1_ucm_max_lemma_size               10
% 23.50/3.50  
% 23.50/3.50  ------ AIG Options
% 23.50/3.50  
% 23.50/3.50  --aig_mode                              false
% 23.50/3.50  
% 23.50/3.50  ------ Instantiation Options
% 23.50/3.50  
% 23.50/3.50  --instantiation_flag                    true
% 23.50/3.50  --inst_sos_flag                         true
% 23.50/3.50  --inst_sos_phase                        true
% 23.50/3.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 23.50/3.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 23.50/3.50  --inst_lit_sel_side                     none
% 23.50/3.50  --inst_solver_per_active                1400
% 23.50/3.50  --inst_solver_calls_frac                1.
% 23.50/3.50  --inst_passive_queue_type               priority_queues
% 23.50/3.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 23.50/3.50  --inst_passive_queues_freq              [25;2]
% 23.50/3.50  --inst_dismatching                      true
% 23.50/3.50  --inst_eager_unprocessed_to_passive     true
% 23.50/3.50  --inst_prop_sim_given                   true
% 23.50/3.50  --inst_prop_sim_new                     false
% 23.50/3.50  --inst_subs_new                         false
% 23.50/3.50  --inst_eq_res_simp                      false
% 23.50/3.50  --inst_subs_given                       false
% 23.50/3.50  --inst_orphan_elimination               true
% 23.50/3.50  --inst_learning_loop_flag               true
% 23.50/3.50  --inst_learning_start                   3000
% 23.50/3.50  --inst_learning_factor                  2
% 23.50/3.50  --inst_start_prop_sim_after_learn       3
% 23.50/3.50  --inst_sel_renew                        solver
% 23.50/3.50  --inst_lit_activity_flag                true
% 23.50/3.50  --inst_restr_to_given                   false
% 23.50/3.50  --inst_activity_threshold               500
% 23.50/3.50  --inst_out_proof                        true
% 23.50/3.50  
% 23.50/3.50  ------ Resolution Options
% 23.50/3.50  
% 23.50/3.50  --resolution_flag                       false
% 23.50/3.50  --res_lit_sel                           adaptive
% 23.50/3.50  --res_lit_sel_side                      none
% 23.50/3.50  --res_ordering                          kbo
% 23.50/3.50  --res_to_prop_solver                    active
% 23.50/3.50  --res_prop_simpl_new                    false
% 23.50/3.50  --res_prop_simpl_given                  true
% 23.50/3.50  --res_passive_queue_type                priority_queues
% 23.50/3.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 23.50/3.50  --res_passive_queues_freq               [15;5]
% 23.50/3.50  --res_forward_subs                      full
% 23.50/3.50  --res_backward_subs                     full
% 23.50/3.50  --res_forward_subs_resolution           true
% 23.50/3.50  --res_backward_subs_resolution          true
% 23.50/3.50  --res_orphan_elimination                true
% 23.50/3.50  --res_time_limit                        2.
% 23.50/3.50  --res_out_proof                         true
% 23.50/3.50  
% 23.50/3.50  ------ Superposition Options
% 23.50/3.50  
% 23.50/3.50  --superposition_flag                    true
% 23.50/3.50  --sup_passive_queue_type                priority_queues
% 23.50/3.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 23.50/3.50  --sup_passive_queues_freq               [8;1;4]
% 23.50/3.50  --demod_completeness_check              fast
% 23.50/3.50  --demod_use_ground                      true
% 23.50/3.50  --sup_to_prop_solver                    passive
% 23.50/3.50  --sup_prop_simpl_new                    true
% 23.50/3.50  --sup_prop_simpl_given                  true
% 23.50/3.50  --sup_fun_splitting                     true
% 23.50/3.50  --sup_smt_interval                      50000
% 23.50/3.50  
% 23.50/3.50  ------ Superposition Simplification Setup
% 23.50/3.50  
% 23.50/3.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 23.50/3.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 23.50/3.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 23.50/3.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 23.50/3.50  --sup_full_triv                         [TrivRules;PropSubs]
% 23.50/3.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 23.50/3.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 23.50/3.50  --sup_immed_triv                        [TrivRules]
% 23.50/3.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_immed_bw_main                     []
% 23.50/3.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 23.50/3.50  --sup_input_triv                        [Unflattening;TrivRules]
% 23.50/3.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 23.50/3.50  --sup_input_bw                          []
% 23.50/3.50  
% 23.50/3.50  ------ Combination Options
% 23.50/3.50  
% 23.50/3.50  --comb_res_mult                         3
% 23.50/3.50  --comb_sup_mult                         2
% 23.50/3.50  --comb_inst_mult                        10
% 23.50/3.50  
% 23.50/3.50  ------ Debug Options
% 23.50/3.50  
% 23.50/3.50  --dbg_backtrace                         false
% 23.50/3.50  --dbg_dump_prop_clauses                 false
% 23.50/3.50  --dbg_dump_prop_clauses_file            -
% 23.50/3.50  --dbg_out_stat                          false
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  ------ Proving...
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  % SZS status Theorem for theBenchmark.p
% 23.50/3.50  
% 23.50/3.50  % SZS output start CNFRefutation for theBenchmark.p
% 23.50/3.50  
% 23.50/3.50  fof(f30,conjecture,(
% 23.50/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0)) => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f31,negated_conjecture,(
% 23.50/3.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0)) => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 23.50/3.50    inference(negated_conjecture,[],[f30])).
% 23.50/3.50  
% 23.50/3.50  fof(f61,plain,(
% 23.50/3.50    ? [X0] : (? [X1] : (? [X2] : ((~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & (v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f31])).
% 23.50/3.50  
% 23.50/3.50  fof(f62,plain,(
% 23.50/3.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 23.50/3.50    inference(flattening,[],[f61])).
% 23.50/3.50  
% 23.50/3.50  fof(f70,plain,(
% 23.50/3.50    ( ! [X0,X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,sK2),X0) & v4_pre_topc(sK2,X0) & v2_tops_1(sK2,X0) & v2_tops_1(X1,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.50/3.50    introduced(choice_axiom,[])).
% 23.50/3.50  
% 23.50/3.50  fof(f69,plain,(
% 23.50/3.50    ( ! [X0] : (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),sK1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(sK1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 23.50/3.50    introduced(choice_axiom,[])).
% 23.50/3.50  
% 23.50/3.50  fof(f68,plain,(
% 23.50/3.50    ? [X0] : (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) & v4_pre_topc(X2,X0) & v2_tops_1(X2,X0) & v2_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v4_pre_topc(X2,sK0) & v2_tops_1(X2,sK0) & v2_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 23.50/3.50    introduced(choice_axiom,[])).
% 23.50/3.50  
% 23.50/3.50  fof(f71,plain,(
% 23.50/3.50    ((~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v4_pre_topc(sK2,sK0) & v2_tops_1(sK2,sK0) & v2_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 23.50/3.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f62,f70,f69,f68])).
% 23.50/3.50  
% 23.50/3.50  fof(f108,plain,(
% 23.50/3.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f20,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f49,plain,(
% 23.50/3.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f20])).
% 23.50/3.50  
% 23.50/3.50  fof(f91,plain,(
% 23.50/3.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f49])).
% 23.50/3.50  
% 23.50/3.50  fof(f19,axiom,(
% 23.50/3.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f48,plain,(
% 23.50/3.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f19])).
% 23.50/3.50  
% 23.50/3.50  fof(f90,plain,(
% 23.50/3.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f48])).
% 23.50/3.50  
% 23.50/3.50  fof(f106,plain,(
% 23.50/3.50    l1_pre_topc(sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f8,axiom,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f37,plain,(
% 23.50/3.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f8])).
% 23.50/3.50  
% 23.50/3.50  fof(f79,plain,(
% 23.50/3.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f37])).
% 23.50/3.50  
% 23.50/3.50  fof(f9,axiom,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f38,plain,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f9])).
% 23.50/3.50  
% 23.50/3.50  fof(f80,plain,(
% 23.50/3.50    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f38])).
% 23.50/3.50  
% 23.50/3.50  fof(f107,plain,(
% 23.50/3.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f10,axiom,(
% 23.50/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f39,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.50/3.50    inference(ennf_transformation,[],[f10])).
% 23.50/3.50  
% 23.50/3.50  fof(f40,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(flattening,[],[f39])).
% 23.50/3.50  
% 23.50/3.50  fof(f81,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f40])).
% 23.50/3.50  
% 23.50/3.50  fof(f22,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f51,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f22])).
% 23.50/3.50  
% 23.50/3.50  fof(f93,plain,(
% 23.50/3.50    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f51])).
% 23.50/3.50  
% 23.50/3.50  fof(f11,axiom,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f41,plain,(
% 23.50/3.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f11])).
% 23.50/3.50  
% 23.50/3.50  fof(f82,plain,(
% 23.50/3.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f41])).
% 23.50/3.50  
% 23.50/3.50  fof(f12,axiom,(
% 23.50/3.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f42,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 23.50/3.50    inference(ennf_transformation,[],[f12])).
% 23.50/3.50  
% 23.50/3.50  fof(f43,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(flattening,[],[f42])).
% 23.50/3.50  
% 23.50/3.50  fof(f83,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f43])).
% 23.50/3.50  
% 23.50/3.50  fof(f7,axiom,(
% 23.50/3.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f36,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f7])).
% 23.50/3.50  
% 23.50/3.50  fof(f78,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f36])).
% 23.50/3.50  
% 23.50/3.50  fof(f109,plain,(
% 23.50/3.50    v2_tops_1(sK1,sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f28,axiom,(
% 23.50/3.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f58,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f28])).
% 23.50/3.50  
% 23.50/3.50  fof(f59,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 23.50/3.50    inference(flattening,[],[f58])).
% 23.50/3.50  
% 23.50/3.50  fof(f102,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f59])).
% 23.50/3.50  
% 23.50/3.50  fof(f105,plain,(
% 23.50/3.50    v2_pre_topc(sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f27,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f57,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f27])).
% 23.50/3.50  
% 23.50/3.50  fof(f66,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(nnf_transformation,[],[f57])).
% 23.50/3.50  
% 23.50/3.50  fof(f100,plain,(
% 23.50/3.50    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f66])).
% 23.50/3.50  
% 23.50/3.50  fof(f111,plain,(
% 23.50/3.50    v4_pre_topc(sK2,sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f24,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f53,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f24])).
% 23.50/3.50  
% 23.50/3.50  fof(f65,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(nnf_transformation,[],[f53])).
% 23.50/3.50  
% 23.50/3.50  fof(f96,plain,(
% 23.50/3.50    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f65])).
% 23.50/3.50  
% 23.50/3.50  fof(f110,plain,(
% 23.50/3.50    v2_tops_1(sK2,sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f23,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f52,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f23])).
% 23.50/3.50  
% 23.50/3.50  fof(f64,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(nnf_transformation,[],[f52])).
% 23.50/3.50  
% 23.50/3.50  fof(f94,plain,(
% 23.50/3.50    ( ! [X0,X1] : (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f64])).
% 23.50/3.50  
% 23.50/3.50  fof(f14,axiom,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f45,plain,(
% 23.50/3.50    ! [X0,X1] : (! [X2] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f14])).
% 23.50/3.50  
% 23.50/3.50  fof(f85,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f45])).
% 23.50/3.50  
% 23.50/3.50  fof(f13,axiom,(
% 23.50/3.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f44,plain,(
% 23.50/3.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f13])).
% 23.50/3.50  
% 23.50/3.50  fof(f84,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f44])).
% 23.50/3.50  
% 23.50/3.50  fof(f3,axiom,(
% 23.50/3.50    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f74,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f3])).
% 23.50/3.50  
% 23.50/3.50  fof(f15,axiom,(
% 23.50/3.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f46,plain,(
% 23.50/3.50    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.50/3.50    inference(ennf_transformation,[],[f15])).
% 23.50/3.50  
% 23.50/3.50  fof(f86,plain,(
% 23.50/3.50    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f46])).
% 23.50/3.50  
% 23.50/3.50  fof(f17,axiom,(
% 23.50/3.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f89,plain,(
% 23.50/3.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 23.50/3.50    inference(cnf_transformation,[],[f17])).
% 23.50/3.50  
% 23.50/3.50  fof(f4,axiom,(
% 23.50/3.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f75,plain,(
% 23.50/3.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f4])).
% 23.50/3.50  
% 23.50/3.50  fof(f6,axiom,(
% 23.50/3.50    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f35,plain,(
% 23.50/3.50    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 23.50/3.50    inference(ennf_transformation,[],[f6])).
% 23.50/3.50  
% 23.50/3.50  fof(f77,plain,(
% 23.50/3.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f35])).
% 23.50/3.50  
% 23.50/3.50  fof(f1,axiom,(
% 23.50/3.50    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f72,plain,(
% 23.50/3.50    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 23.50/3.50    inference(cnf_transformation,[],[f1])).
% 23.50/3.50  
% 23.50/3.50  fof(f112,plain,(
% 23.50/3.50    ~v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 23.50/3.50    inference(cnf_transformation,[],[f71])).
% 23.50/3.50  
% 23.50/3.50  fof(f29,axiom,(
% 23.50/3.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 23.50/3.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.50/3.50  
% 23.50/3.50  fof(f60,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(ennf_transformation,[],[f29])).
% 23.50/3.50  
% 23.50/3.50  fof(f67,plain,(
% 23.50/3.50    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 23.50/3.50    inference(nnf_transformation,[],[f60])).
% 23.50/3.50  
% 23.50/3.50  fof(f104,plain,(
% 23.50/3.50    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 23.50/3.50    inference(cnf_transformation,[],[f67])).
% 23.50/3.50  
% 23.50/3.50  cnf(c_37,negated_conjecture,
% 23.50/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.50/3.50      inference(cnf_transformation,[],[f108]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1710,plain,
% 23.50/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_19,plain,
% 23.50/3.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f91]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_18,plain,
% 23.50/3.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f90]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_447,plain,
% 23.50/3.50      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 23.50/3.50      inference(resolution,[status(thm)],[c_19,c_18]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_39,negated_conjecture,
% 23.50/3.50      ( l1_pre_topc(sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f106]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_571,plain,
% 23.50/3.50      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_447,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_572,plain,
% 23.50/3.50      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_571]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1725,plain,
% 23.50/3.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_1710,c_572]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_7,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f79]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1719,plain,
% 23.50/3.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4293,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),sK2) = k4_xboole_0(k2_struct_0(sK0),sK2) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_1719]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 23.50/3.50      inference(cnf_transformation,[],[f80]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1718,plain,
% 23.50/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.50/3.50      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_5266,plain,
% 23.50/3.50      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.50/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_4293,c_1718]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23466,plain,
% 23.50/3.50      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_5266,c_1725]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_38,negated_conjecture,
% 23.50/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.50/3.50      inference(cnf_transformation,[],[f107]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1709,plain,
% 23.50/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1724,plain,
% 23.50/3.50      ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_1709,c_572]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_9,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.50/3.50      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 23.50/3.50      inference(cnf_transformation,[],[f81]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1717,plain,
% 23.50/3.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.50/3.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 23.50/3.50      | m1_subset_1(k4_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_21,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ l1_pre_topc(X1)
% 23.50/3.50      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f93]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_695,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 23.50/3.50      | sK0 != X1 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_696,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_695]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1705,plain,
% 23.50/3.50      ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1732,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),X0))) = k1_tops_1(sK0,X0)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_1705,c_572]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_2570,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),X0,X1)))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),X0,X1))
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1717,c_1732]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_7086,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,X0)))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,X0))
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_2570]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_9363,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),X0))))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),X0)))
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1718,c_7086]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_79030,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)))))) = k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)))) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23466,c_9363]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_10,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 23.50/3.50      inference(cnf_transformation,[],[f82]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1716,plain,
% 23.50/3.50      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4280,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2)) = sK2 ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_1716]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_5191,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2)) = sK2 ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_4280,c_4280,c_4293]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_11,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.50/3.50      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f83]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1715,plain,
% 23.50/3.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 23.50/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6585,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_1715]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6855,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_6585]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4292,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),sK1) = k4_xboole_0(k2_struct_0(sK0),sK1) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_1719]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_5247,plain,
% 23.50/3.50      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.50/3.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_4292,c_1718]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23220,plain,
% 23.50/3.50      ( m1_subset_1(k4_xboole_0(k2_struct_0(sK0),sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_5247,c_1724]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f78]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1720,plain,
% 23.50/3.50      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23230,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23220,c_1720]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_36,negated_conjecture,
% 23.50/3.50      ( v2_tops_1(sK1,sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f109]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_30,plain,
% 23.50/3.50      ( ~ v3_pre_topc(X0,X1)
% 23.50/3.50      | ~ v1_tops_1(X2,X1)
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ v2_pre_topc(X1)
% 23.50/3.50      | ~ l1_pre_topc(X1)
% 23.50/3.50      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f102]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40,negated_conjecture,
% 23.50/3.50      ( v2_pre_topc(sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f105]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_480,plain,
% 23.50/3.50      ( ~ v3_pre_topc(X0,X1)
% 23.50/3.50      | ~ v1_tops_1(X2,X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ l1_pre_topc(X1)
% 23.50/3.50      | k2_pre_topc(X1,k9_subset_1(u1_struct_0(X1),X0,X2)) = k2_pre_topc(X1,X0)
% 23.50/3.50      | sK0 != X1 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_30,c_40]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_481,plain,
% 23.50/3.50      ( ~ v3_pre_topc(X0,sK0)
% 23.50/3.50      | ~ v1_tops_1(X1,sK0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ l1_pre_topc(sK0)
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_480]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_485,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ v1_tops_1(X1,sK0)
% 23.50/3.50      | ~ v3_pre_topc(X0,sK0)
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_481,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_486,plain,
% 23.50/3.50      ( ~ v3_pre_topc(X0,sK0)
% 23.50/3.50      | ~ v1_tops_1(X1,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) = k2_pre_topc(sK0,X0) ),
% 23.50/3.50      inference(renaming,[status(thm)],[c_485]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_29,plain,
% 23.50/3.50      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 23.50/3.50      | ~ v4_pre_topc(X1,X0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.50/3.50      | ~ l1_pre_topc(X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f100]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_34,negated_conjecture,
% 23.50/3.50      ( v4_pre_topc(sK2,sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f111]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_535,plain,
% 23.50/3.50      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 23.50/3.50      | ~ l1_pre_topc(X0)
% 23.50/3.50      | sK2 != X1
% 23.50/3.50      | sK0 != X0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_29,c_34]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_536,plain,
% 23.50/3.50      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
% 23.50/3.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ l1_pre_topc(sK0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_535]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_538,plain,
% 23.50/3.50      ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_536,c_39,c_37]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_548,plain,
% 23.50/3.50      ( ~ v1_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)) = k2_pre_topc(sK0,X1)
% 23.50/3.50      | k3_subset_1(u1_struct_0(sK0),sK2) != X1
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_486,c_538]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_549,plain,
% 23.50/3.50      ( ~ v1_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),X0)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_548]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_25,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,X1)
% 23.50/3.50      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ l1_pre_topc(X1) ),
% 23.50/3.50      inference(cnf_transformation,[],[f96]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_635,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,X1)
% 23.50/3.50      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | sK0 != X1 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_25,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_636,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_635]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_801,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),X1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
% 23.50/3.50      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_549,c_636]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_802,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_801]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_816,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 23.50/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_802,c_8]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_970,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),X0))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
% 23.50/3.50      | sK1 != X0
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_36,c_816]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_971,plain,
% 23.50/3.50      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_970]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_973,plain,
% 23.50/3.50      ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_971,c_38]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1696,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2),k3_subset_1(u1_struct_0(sK0),sK1))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2))
% 23.50/3.50      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_973]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_35,negated_conjecture,
% 23.50/3.50      ( v2_tops_1(sK2,sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f110]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23,plain,
% 23.50/3.50      ( ~ v1_tops_1(X0,X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ l1_pre_topc(X1)
% 23.50/3.50      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 23.50/3.50      inference(cnf_transformation,[],[f94]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_665,plain,
% 23.50/3.50      ( ~ v1_tops_1(X0,X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | k2_pre_topc(X1,X0) = k2_struct_0(X1)
% 23.50/3.50      | sK0 != X1 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_23,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_666,plain,
% 23.50/3.50      ( ~ v1_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_665]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_781,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,X1) = k2_struct_0(sK0)
% 23.50/3.50      | k3_subset_1(u1_struct_0(sK0),X0) != X1
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_666,c_636]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_782,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_781]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_794,plain,
% 23.50/3.50      ( ~ v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(forward_subsumption_resolution,[status(thm)],[c_782,c_8]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_954,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k2_struct_0(sK0)
% 23.50/3.50      | sK2 != X0
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_35,c_794]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_955,plain,
% 23.50/3.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_954]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_957,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_955,c_37]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1729,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k3_subset_1(k2_struct_0(sK0),sK2)) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_957,c_572]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1737,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0)
% 23.50/3.50      | m1_subset_1(k3_subset_1(k2_struct_0(sK0),sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_1696,c_572,c_1729]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4130,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0)
% 23.50/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1718,c_1737]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8420,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK2),k3_subset_1(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_4130,c_1725]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8422,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1))) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_8420,c_4292,c_4293]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_30929,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2))) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_23230,c_8422]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_13,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.50/3.50      | k9_subset_1(X1,X2,k3_subset_1(X1,X0)) = k7_subset_1(X1,X2,X0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f85]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1713,plain,
% 23.50/3.50      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
% 23.50/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8328,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),X0,sK2)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_1713]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8329,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),X0,sK2)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_8328,c_4293]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_27768,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23220,c_8329]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_12,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 23.50/3.50      inference(cnf_transformation,[],[f84]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1714,plain,
% 23.50/3.50      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23231,plain,
% 23.50/3.50      ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK1),X0) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23220,c_1714]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_2,plain,
% 23.50/3.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 23.50/3.50      inference(cnf_transformation,[],[f74]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23266,plain,
% 23.50/3.50      ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,X0)) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_23231,c_2]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_27775,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_27768,c_23266]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_30930,plain,
% 23.50/3.50      ( k2_pre_topc(sK0,k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_struct_0(sK0) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_30929,c_27775]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6584,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),X0,sK1) = k2_xboole_0(X0,sK1)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_1715]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6727,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),sK2,sK1) = k2_xboole_0(sK2,sK1) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_6584]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6848,plain,
% 23.50/3.50      ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.50/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.50/3.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_6727,c_1717]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40093,plain,
% 23.50/3.50      ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 23.50/3.50      inference(global_propositional_subsumption,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_6848,c_1724,c_1725]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40111,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_40093,c_1719]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23476,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK2)) = k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23466,c_1720]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8327,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),X0,k3_subset_1(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_1713]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8330,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),X0,k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),X0,sK1)
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_8327,c_4292]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_30641,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1)) = k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),sK1) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23466,c_8330]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23477,plain,
% 23.50/3.50      ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) = k4_xboole_0(k4_xboole_0(k2_struct_0(sK0),sK2),X0) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23466,c_1714]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23512,plain,
% 23.50/3.50      ( k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),X0) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,X0)) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_23477,c_2]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_30650,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK2),k4_xboole_0(k2_struct_0(sK0),sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_30641,c_23512]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_33767,plain,
% 23.50/3.50      ( k9_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),k4_xboole_0(k2_struct_0(sK0),sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23476,c_30650]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_33771,plain,
% 23.50/3.50      ( k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_33767,c_27775]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40166,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_40111,c_33771]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40112,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK2,sK1))) = k2_xboole_0(sK2,sK1) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_40093,c_1716]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40169,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK2,sK1) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_40166,c_40112]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_14,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.50/3.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 23.50/3.50      | k4_subset_1(X1,k3_subset_1(X1,X2),X0) = k3_subset_1(X1,k7_subset_1(X1,X2,X0)) ),
% 23.50/3.50      inference(cnf_transformation,[],[f86]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1712,plain,
% 23.50/3.50      ( k4_subset_1(X0,k3_subset_1(X0,X1),X2) = k3_subset_1(X0,k7_subset_1(X0,X1,X2))
% 23.50/3.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 23.50/3.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_8403,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),X0),sK2) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),X0,sK2))
% 23.50/3.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1725,c_1712]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23242,plain,
% 23.50/3.50      ( k4_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)),sK2) = k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2)) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_23220,c_8403]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4279,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k3_subset_1(k2_struct_0(sK0),sK1)) = sK1 ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1724,c_1716]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_5184,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) = sK1 ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_4279,c_4279,c_4292]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23259,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k7_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1),sK2)) = k2_xboole_0(sK1,sK2) ),
% 23.50/3.50      inference(light_normalisation,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_23242,c_5184,c_6855]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_23267,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2))) = k2_xboole_0(sK1,sK2) ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_23266,c_23259]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40174,plain,
% 23.50/3.50      ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK2,sK1) ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_40169,c_23267]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_40503,plain,
% 23.50/3.50      ( k3_subset_1(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) = k4_xboole_0(k2_struct_0(sK0),k2_xboole_0(sK1,sK2)) ),
% 23.50/3.50      inference(light_normalisation,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_40111,c_33771,c_40174]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_79048,plain,
% 23.50/3.50      ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k3_subset_1(k2_struct_0(sK0),k2_struct_0(sK0)) ),
% 23.50/3.50      inference(light_normalisation,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_79030,c_5191,c_6855,c_30930,c_40503]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_17,plain,
% 23.50/3.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 23.50/3.50      inference(cnf_transformation,[],[f89]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1711,plain,
% 23.50/3.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4278,plain,
% 23.50/3.50      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1711,c_1716]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4291,plain,
% 23.50/3.50      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1711,c_1719]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_3,plain,
% 23.50/3.50      ( r1_xboole_0(X0,k1_xboole_0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f75]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1723,plain,
% 23.50/3.50      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_5,plain,
% 23.50/3.50      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ),
% 23.50/3.50      inference(cnf_transformation,[],[f77]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1721,plain,
% 23.50/3.50      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
% 23.50/3.50      | r1_xboole_0(X0,X1) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_2744,plain,
% 23.50/3.50      ( k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_1723,c_1721]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_0,plain,
% 23.50/3.50      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.50/3.50      inference(cnf_transformation,[],[f72]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_2745,plain,
% 23.50/3.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_2744,c_0]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_4294,plain,
% 23.50/3.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_4291,c_2745]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_9133,plain,
% 23.50/3.50      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_4278,c_4278,c_4294]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_79049,plain,
% 23.50/3.50      ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_79048,c_9133]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6900,plain,
% 23.50/3.50      ( m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 23.50/3.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top
% 23.50/3.50      | m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(superposition,[status(thm)],[c_6855,c_1717]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_33,negated_conjecture,
% 23.50/3.50      ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
% 23.50/3.50      inference(cnf_transformation,[],[f112]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_31,plain,
% 23.50/3.50      ( v2_tops_1(X0,X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | ~ l1_pre_topc(X1)
% 23.50/3.50      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 23.50/3.50      inference(cnf_transformation,[],[f104]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_608,plain,
% 23.50/3.50      ( v2_tops_1(X0,X1)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 23.50/3.50      | k1_tops_1(X1,X0) != k1_xboole_0
% 23.50/3.50      | sK0 != X1 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_31,c_39]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_609,plain,
% 23.50/3.50      ( v2_tops_1(X0,sK0)
% 23.50/3.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k1_tops_1(sK0,X0) != k1_xboole_0 ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_608]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_930,plain,
% 23.50/3.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k4_subset_1(u1_struct_0(sK0),sK1,sK2) != X0
% 23.50/3.50      | k1_tops_1(sK0,X0) != k1_xboole_0
% 23.50/3.50      | sK0 != sK0 ),
% 23.50/3.50      inference(resolution_lifted,[status(thm)],[c_33,c_609]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_931,plain,
% 23.50/3.50      ( ~ m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
% 23.50/3.50      | k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_xboole_0 ),
% 23.50/3.50      inference(unflattening,[status(thm)],[c_930]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1698,plain,
% 23.50/3.50      ( k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) != k1_xboole_0
% 23.50/3.50      | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_1733,plain,
% 23.50/3.50      ( k1_tops_1(sK0,k4_subset_1(k2_struct_0(sK0),sK1,sK2)) != k1_xboole_0
% 23.50/3.50      | m1_subset_1(k4_subset_1(k2_struct_0(sK0),sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(light_normalisation,[status(thm)],[c_1698,c_572]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(c_6894,plain,
% 23.50/3.50      ( k1_tops_1(sK0,k2_xboole_0(sK1,sK2)) != k1_xboole_0
% 23.50/3.50      | m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) != iProver_top ),
% 23.50/3.50      inference(demodulation,[status(thm)],[c_6855,c_1733]) ).
% 23.50/3.50  
% 23.50/3.50  cnf(contradiction,plain,
% 23.50/3.50      ( $false ),
% 23.50/3.50      inference(minisat,
% 23.50/3.50                [status(thm)],
% 23.50/3.50                [c_79049,c_6900,c_6894,c_1725,c_1724]) ).
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  % SZS output end CNFRefutation for theBenchmark.p
% 23.50/3.50  
% 23.50/3.50  ------                               Statistics
% 23.50/3.50  
% 23.50/3.50  ------ General
% 23.50/3.50  
% 23.50/3.50  abstr_ref_over_cycles:                  0
% 23.50/3.50  abstr_ref_under_cycles:                 0
% 23.50/3.50  gc_basic_clause_elim:                   0
% 23.50/3.50  forced_gc_time:                         0
% 23.50/3.50  parsing_time:                           0.01
% 23.50/3.50  unif_index_cands_time:                  0.
% 23.50/3.50  unif_index_add_time:                    0.
% 23.50/3.50  orderings_time:                         0.
% 23.50/3.50  out_proof_time:                         0.019
% 23.50/3.50  total_time:                             2.589
% 23.50/3.50  num_of_symbols:                         56
% 23.50/3.50  num_of_terms:                           135581
% 23.50/3.50  
% 23.50/3.50  ------ Preprocessing
% 23.50/3.50  
% 23.50/3.50  num_of_splits:                          0
% 23.50/3.50  num_of_split_atoms:                     0
% 23.50/3.50  num_of_reused_defs:                     0
% 23.50/3.50  num_eq_ax_congr_red:                    20
% 23.50/3.50  num_of_sem_filtered_clauses:            1
% 23.50/3.50  num_of_subtypes:                        0
% 23.50/3.50  monotx_restored_types:                  0
% 23.50/3.50  sat_num_of_epr_types:                   0
% 23.50/3.50  sat_num_of_non_cyclic_types:            0
% 23.50/3.50  sat_guarded_non_collapsed_types:        0
% 23.50/3.50  num_pure_diseq_elim:                    0
% 23.50/3.50  simp_replaced_by:                       0
% 23.50/3.50  res_preprocessed:                       184
% 23.50/3.50  prep_upred:                             0
% 23.50/3.50  prep_unflattend:                        29
% 23.50/3.50  smt_new_axioms:                         0
% 23.50/3.50  pred_elim_cands:                        2
% 23.50/3.50  pred_elim:                              8
% 23.50/3.50  pred_elim_cl:                           3
% 23.50/3.50  pred_elim_cycles:                       10
% 23.50/3.50  merged_defs:                            0
% 23.50/3.50  merged_defs_ncl:                        0
% 23.50/3.50  bin_hyper_res:                          0
% 23.50/3.50  prep_cycles:                            4
% 23.50/3.50  pred_elim_time:                         0.02
% 23.50/3.50  splitting_time:                         0.
% 23.50/3.50  sem_filter_time:                        0.
% 23.50/3.50  monotx_time:                            0.
% 23.50/3.50  subtype_inf_time:                       0.
% 23.50/3.50  
% 23.50/3.50  ------ Problem properties
% 23.50/3.50  
% 23.50/3.50  clauses:                                38
% 23.50/3.50  conjectures:                            2
% 23.50/3.50  epr:                                    1
% 23.50/3.50  horn:                                   38
% 23.50/3.50  ground:                                 14
% 23.50/3.50  unary:                                  14
% 23.50/3.50  binary:                                 14
% 23.50/3.50  lits:                                   76
% 23.50/3.50  lits_eq:                                37
% 23.50/3.50  fd_pure:                                0
% 23.50/3.50  fd_pseudo:                              0
% 23.50/3.50  fd_cond:                                0
% 23.50/3.50  fd_pseudo_cond:                         1
% 23.50/3.50  ac_symbols:                             0
% 23.50/3.50  
% 23.50/3.50  ------ Propositional Solver
% 23.50/3.50  
% 23.50/3.50  prop_solver_calls:                      42
% 23.50/3.50  prop_fast_solver_calls:                 2265
% 23.50/3.50  smt_solver_calls:                       0
% 23.50/3.50  smt_fast_solver_calls:                  0
% 23.50/3.50  prop_num_of_clauses:                    24041
% 23.50/3.50  prop_preprocess_simplified:             43040
% 23.50/3.50  prop_fo_subsumed:                       73
% 23.50/3.50  prop_solver_time:                       0.
% 23.50/3.50  smt_solver_time:                        0.
% 23.50/3.50  smt_fast_solver_time:                   0.
% 23.50/3.50  prop_fast_solver_time:                  0.
% 23.50/3.50  prop_unsat_core_time:                   0.003
% 23.50/3.50  
% 23.50/3.50  ------ QBF
% 23.50/3.50  
% 23.50/3.50  qbf_q_res:                              0
% 23.50/3.50  qbf_num_tautologies:                    0
% 23.50/3.50  qbf_prep_cycles:                        0
% 23.50/3.50  
% 23.50/3.50  ------ BMC1
% 23.50/3.50  
% 23.50/3.50  bmc1_current_bound:                     -1
% 23.50/3.50  bmc1_last_solved_bound:                 -1
% 23.50/3.50  bmc1_unsat_core_size:                   -1
% 23.50/3.50  bmc1_unsat_core_parents_size:           -1
% 23.50/3.50  bmc1_merge_next_fun:                    0
% 23.50/3.50  bmc1_unsat_core_clauses_time:           0.
% 23.50/3.50  
% 23.50/3.50  ------ Instantiation
% 23.50/3.50  
% 23.50/3.50  inst_num_of_clauses:                    1743
% 23.50/3.50  inst_num_in_passive:                    1066
% 23.50/3.50  inst_num_in_active:                     3521
% 23.50/3.50  inst_num_in_unprocessed:                32
% 23.50/3.50  inst_num_of_loops:                      3649
% 23.50/3.50  inst_num_of_learning_restarts:          1
% 23.50/3.50  inst_num_moves_active_passive:          124
% 23.50/3.50  inst_lit_activity:                      0
% 23.50/3.50  inst_lit_activity_moves:                3
% 23.50/3.50  inst_num_tautologies:                   0
% 23.50/3.50  inst_num_prop_implied:                  0
% 23.50/3.50  inst_num_existing_simplified:           0
% 23.50/3.50  inst_num_eq_res_simplified:             0
% 23.50/3.50  inst_num_child_elim:                    0
% 23.50/3.50  inst_num_of_dismatching_blockings:      31540
% 23.50/3.50  inst_num_of_non_proper_insts:           9557
% 23.50/3.50  inst_num_of_duplicates:                 0
% 23.50/3.50  inst_inst_num_from_inst_to_res:         0
% 23.50/3.50  inst_dismatching_checking_time:         0.
% 23.50/3.50  
% 23.50/3.50  ------ Resolution
% 23.50/3.50  
% 23.50/3.50  res_num_of_clauses:                     52
% 23.50/3.50  res_num_in_passive:                     52
% 23.50/3.50  res_num_in_active:                      0
% 23.50/3.50  res_num_of_loops:                       188
% 23.50/3.50  res_forward_subset_subsumed:            201
% 23.50/3.50  res_backward_subset_subsumed:           0
% 23.50/3.50  res_forward_subsumed:                   0
% 23.50/3.50  res_backward_subsumed:                  0
% 23.50/3.50  res_forward_subsumption_resolution:     4
% 23.50/3.50  res_backward_subsumption_resolution:    0
% 23.50/3.50  res_clause_to_clause_subsumption:       13907
% 23.50/3.50  res_orphan_elimination:                 0
% 23.50/3.50  res_tautology_del:                      179
% 23.50/3.50  res_num_eq_res_simplified:              2
% 23.50/3.50  res_num_sel_changes:                    0
% 23.50/3.50  res_moves_from_active_to_pass:          0
% 23.50/3.50  
% 23.50/3.50  ------ Superposition
% 23.50/3.50  
% 23.50/3.50  sup_time_total:                         0.
% 23.50/3.50  sup_time_generating:                    0.
% 23.50/3.50  sup_time_sim_full:                      0.
% 23.50/3.50  sup_time_sim_immed:                     0.
% 23.50/3.50  
% 23.50/3.50  sup_num_of_clauses:                     2774
% 23.50/3.50  sup_num_in_active:                      572
% 23.50/3.50  sup_num_in_passive:                     2202
% 23.50/3.50  sup_num_of_loops:                       728
% 23.50/3.50  sup_fw_superposition:                   3531
% 23.50/3.50  sup_bw_superposition:                   3022
% 23.50/3.50  sup_immediate_simplified:               3912
% 23.50/3.50  sup_given_eliminated:                   2
% 23.50/3.50  comparisons_done:                       0
% 23.50/3.50  comparisons_avoided:                    0
% 23.50/3.50  
% 23.50/3.50  ------ Simplifications
% 23.50/3.50  
% 23.50/3.50  
% 23.50/3.50  sim_fw_subset_subsumed:                 55
% 23.50/3.50  sim_bw_subset_subsumed:                 8
% 23.50/3.50  sim_fw_subsumed:                        642
% 23.50/3.50  sim_bw_subsumed:                        60
% 23.50/3.50  sim_fw_subsumption_res:                 0
% 23.50/3.50  sim_bw_subsumption_res:                 0
% 23.50/3.50  sim_tautology_del:                      14
% 23.50/3.50  sim_eq_tautology_del:                   926
% 23.50/3.50  sim_eq_res_simp:                        5
% 23.50/3.50  sim_fw_demodulated:                     1574
% 23.50/3.50  sim_bw_demodulated:                     274
% 23.50/3.50  sim_light_normalised:                   1965
% 23.50/3.50  sim_joinable_taut:                      0
% 23.50/3.50  sim_joinable_simp:                      0
% 23.50/3.50  sim_ac_normalised:                      0
% 23.50/3.50  sim_smt_subsumption:                    0
% 23.50/3.50  
%------------------------------------------------------------------------------
