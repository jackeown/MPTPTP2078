%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:24 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  240 (2092 expanded)
%              Number of clauses        :  123 ( 502 expanded)
%              Number of leaves         :   33 ( 476 expanded)
%              Depth                    :   28
%              Number of atoms          :  669 (10327 expanded)
%              Number of equality atoms :  246 (2751 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f30,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k2_tops_1(X0,sK2) != sK2
          | ~ v3_tops_1(sK2,X0) )
        & ( k2_tops_1(X0,sK2) = sK2
          | v3_tops_1(sK2,X0) )
        & v4_pre_topc(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK1,X1) != X1
            | ~ v3_tops_1(X1,sK1) )
          & ( k2_tops_1(sK1,X1) = X1
            | v3_tops_1(X1,sK1) )
          & v4_pre_topc(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,
    ( ( k2_tops_1(sK1,sK2) != sK2
      | ~ v3_tops_1(sK2,sK1) )
    & ( k2_tops_1(sK1,sK2) = sK2
      | v3_tops_1(sK2,sK1) )
    & v4_pre_topc(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f69,f71,f70])).

fof(f111,plain,(
    v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f109,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f110,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f72])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f126,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f78,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,
    ( k2_tops_1(sK1,sK2) = sK2
    | v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f114,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f86,f87])).

fof(f115,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f85,f114])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f84,f115])).

fof(f117,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f116])).

fof(f118,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f82,f117])).

fof(f119,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f94,f118])).

fof(f120,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f79,f119])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f88,f120])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f122,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f81,f120])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f92,f119])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f59])).

fof(f61,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f60,f61])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f80,f119])).

fof(f113,plain,
    ( k2_tops_1(sK1,sK2) != sK2
    | ~ v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f72])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1815,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_25,plain,
    ( ~ v3_tops_1(X0,X1)
    | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_441,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | X1 != X3
    | k2_pre_topc(X3,X2) = k2_struct_0(X3)
    | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_442,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_441])).

cnf(c_456,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_442,c_9])).

cnf(c_27,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_30,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_414,plain,
    ( v3_tops_1(X0,X1)
    | ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_30])).

cnf(c_415,plain,
    ( v3_tops_1(sK2,sK1)
    | ~ v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_32,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_417,plain,
    ( v3_tops_1(sK2,sK1)
    | ~ v2_tops_1(sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_415,c_32,c_31])).

cnf(c_479,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_417])).

cnf(c_480,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_32,c_31])).

cnf(c_23,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_546,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,k2_tops_1(X1,X0))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_547,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_tops_1(sK1,X0)) ),
    inference(unflattening,[status(thm)],[c_546])).

cnf(c_720,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_tops_1(sK1,X0))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_482,c_547])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_723,plain,
    ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_721,c_31])).

cnf(c_1802,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_101,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_105,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_29,negated_conjecture,
    ( v3_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) = sK2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_248,plain,
    ( v3_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) = sK2 ),
    inference(prop_impl,[status(thm)],[c_29])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK1,sK2) = sK2
    | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_456,c_248])).

cnf(c_494,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_tops_1(sK1,sK2) = sK2
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_496,plain,
    ( k2_tops_1(sK1,sK2) = sK2
    | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_32,c_31])).

cnf(c_1235,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1862,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k2_tops_1(sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1235])).

cnf(c_1864,plain,
    ( r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK2)
    | k2_tops_1(sK1,sK2) != sK2
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1862])).

cnf(c_2039,plain,
    ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1802,c_31,c_101,c_105,c_496,c_721,c_1864])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_615,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_615])).

cnf(c_1806,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2043,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2039,c_1806])).

cnf(c_3377,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_2043])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_12228,plain,
    ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3377,c_34])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1814,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12233,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1))) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_12228,c_1814])).

cnf(c_1809,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_32])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_1807,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_1891,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1809,c_1807])).

cnf(c_2042,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = k1_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2039,c_1891])).

cnf(c_22,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_561,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_32])).

cnf(c_562,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_669,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(X0,k2_tops_1(sK1,X0))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_547,c_562])).

cnf(c_671,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_669])).

cnf(c_1097,plain,
    ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_31,c_671])).

cnf(c_1799,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1097])).

cnf(c_26,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_506,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(sK1,sK2) = sK2
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_248])).

cnf(c_507,plain,
    ( v2_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_tops_1(sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_509,plain,
    ( v2_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_32,c_31])).

cnf(c_684,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tops_1(sK1,sK2) = sK2
    | k1_tops_1(sK1,X0) = k1_xboole_0
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_509,c_562])).

cnf(c_685,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tops_1(sK1,sK2) = sK2
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_684])).

cnf(c_687,plain,
    ( k2_tops_1(sK1,sK2) = sK2
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_685,c_31])).

cnf(c_867,plain,
    ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
    | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_31,c_671])).

cnf(c_2119,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1799,c_101,c_105,c_687,c_867,c_1864])).

cnf(c_2256,plain,
    ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2042,c_2042,c_2119])).

cnf(c_12330,plain,
    ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_12233,c_2256])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1811,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1816,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4310,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1811,c_1816])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_4314,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4310,c_7])).

cnf(c_12331,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_12330,c_4314])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_32])).

cnf(c_592,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k2_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1808,plain,
    ( k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k2_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_1944,plain,
    ( k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1809,c_1808])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_30])).

cnf(c_429,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_431,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_32,c_31])).

cnf(c_1946,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k2_tops_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_1944,c_431])).

cnf(c_2041,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_2039,c_1946])).

cnf(c_12562,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,u1_struct_0(sK1)) = k2_tops_1(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_12331,c_2041])).

cnf(c_4324,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4314,c_1815])).

cnf(c_80,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8848,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4324,c_80])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_1812,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8858,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(superposition,[status(thm)],[c_8848,c_1812])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1821,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4199,plain,
    ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1809,c_1813])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1822,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4412,plain,
    ( r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4199,c_1822])).

cnf(c_4600,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1821,c_4412])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1817,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4918,plain,
    ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK1))) = sK2 ),
    inference(superposition,[status(thm)],[c_4600,c_1817])).

cnf(c_10723,plain,
    ( k9_subset_1(u1_struct_0(sK1),sK2,u1_struct_0(sK1)) = sK2 ),
    inference(superposition,[status(thm)],[c_8858,c_4918])).

cnf(c_12565,plain,
    ( k2_tops_1(sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_12562,c_10723])).

cnf(c_28,negated_conjecture,
    ( ~ v3_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) != sK2 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_246,plain,
    ( ~ v3_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) != sK2 ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_469,plain,
    ( ~ v2_tops_1(sK2,sK1)
    | k2_tops_1(sK1,sK2) != sK2 ),
    inference(resolution,[status(thm)],[c_417,c_246])).

cnf(c_21,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_576,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_577,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tops_1(sK1,sK2) != sK2
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | sK2 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_469,c_577])).

cnf(c_735,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_tops_1(sK1,sK2) != sK2
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_734])).

cnf(c_737,plain,
    ( k2_tops_1(sK1,sK2) != sK2
    | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_735,c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12565,c_2119,c_737])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  ------ Input Options
% 3.69/0.99  
% 3.69/0.99  --out_options                           all
% 3.69/0.99  --tptp_safe_out                         true
% 3.69/0.99  --problem_path                          ""
% 3.69/0.99  --include_path                          ""
% 3.69/0.99  --clausifier                            res/vclausify_rel
% 3.69/0.99  --clausifier_options                    ""
% 3.69/0.99  --stdin                                 false
% 3.69/0.99  --stats_out                             all
% 3.69/0.99  
% 3.69/0.99  ------ General Options
% 3.69/0.99  
% 3.69/0.99  --fof                                   false
% 3.69/0.99  --time_out_real                         305.
% 3.69/0.99  --time_out_virtual                      -1.
% 3.69/0.99  --symbol_type_check                     false
% 3.69/0.99  --clausify_out                          false
% 3.69/0.99  --sig_cnt_out                           false
% 3.69/0.99  --trig_cnt_out                          false
% 3.69/0.99  --trig_cnt_out_tolerance                1.
% 3.69/0.99  --trig_cnt_out_sk_spl                   false
% 3.69/0.99  --abstr_cl_out                          false
% 3.69/0.99  
% 3.69/0.99  ------ Global Options
% 3.69/0.99  
% 3.69/0.99  --schedule                              default
% 3.69/0.99  --add_important_lit                     false
% 3.69/0.99  --prop_solver_per_cl                    1000
% 3.69/0.99  --min_unsat_core                        false
% 3.69/0.99  --soft_assumptions                      false
% 3.69/0.99  --soft_lemma_size                       3
% 3.69/0.99  --prop_impl_unit_size                   0
% 3.69/0.99  --prop_impl_unit                        []
% 3.69/0.99  --share_sel_clauses                     true
% 3.69/0.99  --reset_solvers                         false
% 3.69/0.99  --bc_imp_inh                            [conj_cone]
% 3.69/0.99  --conj_cone_tolerance                   3.
% 3.69/0.99  --extra_neg_conj                        none
% 3.69/0.99  --large_theory_mode                     true
% 3.69/0.99  --prolific_symb_bound                   200
% 3.69/0.99  --lt_threshold                          2000
% 3.69/0.99  --clause_weak_htbl                      true
% 3.69/0.99  --gc_record_bc_elim                     false
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing Options
% 3.69/0.99  
% 3.69/0.99  --preprocessing_flag                    true
% 3.69/0.99  --time_out_prep_mult                    0.1
% 3.69/0.99  --splitting_mode                        input
% 3.69/0.99  --splitting_grd                         true
% 3.69/0.99  --splitting_cvd                         false
% 3.69/0.99  --splitting_cvd_svl                     false
% 3.69/0.99  --splitting_nvd                         32
% 3.69/0.99  --sub_typing                            true
% 3.69/0.99  --prep_gs_sim                           true
% 3.69/0.99  --prep_unflatten                        true
% 3.69/0.99  --prep_res_sim                          true
% 3.69/0.99  --prep_upred                            true
% 3.69/0.99  --prep_sem_filter                       exhaustive
% 3.69/0.99  --prep_sem_filter_out                   false
% 3.69/0.99  --pred_elim                             true
% 3.69/0.99  --res_sim_input                         true
% 3.69/0.99  --eq_ax_congr_red                       true
% 3.69/0.99  --pure_diseq_elim                       true
% 3.69/0.99  --brand_transform                       false
% 3.69/0.99  --non_eq_to_eq                          false
% 3.69/0.99  --prep_def_merge                        true
% 3.69/0.99  --prep_def_merge_prop_impl              false
% 3.69/0.99  --prep_def_merge_mbd                    true
% 3.69/0.99  --prep_def_merge_tr_red                 false
% 3.69/0.99  --prep_def_merge_tr_cl                  false
% 3.69/0.99  --smt_preprocessing                     true
% 3.69/0.99  --smt_ac_axioms                         fast
% 3.69/0.99  --preprocessed_out                      false
% 3.69/0.99  --preprocessed_stats                    false
% 3.69/0.99  
% 3.69/0.99  ------ Abstraction refinement Options
% 3.69/0.99  
% 3.69/0.99  --abstr_ref                             []
% 3.69/0.99  --abstr_ref_prep                        false
% 3.69/0.99  --abstr_ref_until_sat                   false
% 3.69/0.99  --abstr_ref_sig_restrict                funpre
% 3.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.99  --abstr_ref_under                       []
% 3.69/0.99  
% 3.69/0.99  ------ SAT Options
% 3.69/0.99  
% 3.69/0.99  --sat_mode                              false
% 3.69/0.99  --sat_fm_restart_options                ""
% 3.69/0.99  --sat_gr_def                            false
% 3.69/0.99  --sat_epr_types                         true
% 3.69/0.99  --sat_non_cyclic_types                  false
% 3.69/0.99  --sat_finite_models                     false
% 3.69/0.99  --sat_fm_lemmas                         false
% 3.69/0.99  --sat_fm_prep                           false
% 3.69/0.99  --sat_fm_uc_incr                        true
% 3.69/0.99  --sat_out_model                         small
% 3.69/0.99  --sat_out_clauses                       false
% 3.69/0.99  
% 3.69/0.99  ------ QBF Options
% 3.69/0.99  
% 3.69/0.99  --qbf_mode                              false
% 3.69/0.99  --qbf_elim_univ                         false
% 3.69/0.99  --qbf_dom_inst                          none
% 3.69/0.99  --qbf_dom_pre_inst                      false
% 3.69/0.99  --qbf_sk_in                             false
% 3.69/0.99  --qbf_pred_elim                         true
% 3.69/0.99  --qbf_split                             512
% 3.69/0.99  
% 3.69/0.99  ------ BMC1 Options
% 3.69/0.99  
% 3.69/0.99  --bmc1_incremental                      false
% 3.69/0.99  --bmc1_axioms                           reachable_all
% 3.69/0.99  --bmc1_min_bound                        0
% 3.69/0.99  --bmc1_max_bound                        -1
% 3.69/0.99  --bmc1_max_bound_default                -1
% 3.69/0.99  --bmc1_symbol_reachability              true
% 3.69/0.99  --bmc1_property_lemmas                  false
% 3.69/0.99  --bmc1_k_induction                      false
% 3.69/0.99  --bmc1_non_equiv_states                 false
% 3.69/0.99  --bmc1_deadlock                         false
% 3.69/0.99  --bmc1_ucm                              false
% 3.69/0.99  --bmc1_add_unsat_core                   none
% 3.69/0.99  --bmc1_unsat_core_children              false
% 3.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.99  --bmc1_out_stat                         full
% 3.69/0.99  --bmc1_ground_init                      false
% 3.69/0.99  --bmc1_pre_inst_next_state              false
% 3.69/0.99  --bmc1_pre_inst_state                   false
% 3.69/0.99  --bmc1_pre_inst_reach_state             false
% 3.69/0.99  --bmc1_out_unsat_core                   false
% 3.69/0.99  --bmc1_aig_witness_out                  false
% 3.69/0.99  --bmc1_verbose                          false
% 3.69/0.99  --bmc1_dump_clauses_tptp                false
% 3.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.99  --bmc1_dump_file                        -
% 3.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.99  --bmc1_ucm_extend_mode                  1
% 3.69/0.99  --bmc1_ucm_init_mode                    2
% 3.69/0.99  --bmc1_ucm_cone_mode                    none
% 3.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.99  --bmc1_ucm_relax_model                  4
% 3.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.99  --bmc1_ucm_layered_model                none
% 3.69/0.99  --bmc1_ucm_max_lemma_size               10
% 3.69/0.99  
% 3.69/0.99  ------ AIG Options
% 3.69/0.99  
% 3.69/0.99  --aig_mode                              false
% 3.69/0.99  
% 3.69/0.99  ------ Instantiation Options
% 3.69/0.99  
% 3.69/0.99  --instantiation_flag                    true
% 3.69/0.99  --inst_sos_flag                         true
% 3.69/0.99  --inst_sos_phase                        true
% 3.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.99  --inst_lit_sel_side                     num_symb
% 3.69/0.99  --inst_solver_per_active                1400
% 3.69/0.99  --inst_solver_calls_frac                1.
% 3.69/0.99  --inst_passive_queue_type               priority_queues
% 3.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.99  --inst_passive_queues_freq              [25;2]
% 3.69/0.99  --inst_dismatching                      true
% 3.69/0.99  --inst_eager_unprocessed_to_passive     true
% 3.69/0.99  --inst_prop_sim_given                   true
% 3.69/0.99  --inst_prop_sim_new                     false
% 3.69/0.99  --inst_subs_new                         false
% 3.69/0.99  --inst_eq_res_simp                      false
% 3.69/0.99  --inst_subs_given                       false
% 3.69/0.99  --inst_orphan_elimination               true
% 3.69/0.99  --inst_learning_loop_flag               true
% 3.69/0.99  --inst_learning_start                   3000
% 3.69/0.99  --inst_learning_factor                  2
% 3.69/0.99  --inst_start_prop_sim_after_learn       3
% 3.69/0.99  --inst_sel_renew                        solver
% 3.69/0.99  --inst_lit_activity_flag                true
% 3.69/0.99  --inst_restr_to_given                   false
% 3.69/0.99  --inst_activity_threshold               500
% 3.69/0.99  --inst_out_proof                        true
% 3.69/0.99  
% 3.69/0.99  ------ Resolution Options
% 3.69/0.99  
% 3.69/0.99  --resolution_flag                       true
% 3.69/0.99  --res_lit_sel                           adaptive
% 3.69/0.99  --res_lit_sel_side                      none
% 3.69/0.99  --res_ordering                          kbo
% 3.69/0.99  --res_to_prop_solver                    active
% 3.69/0.99  --res_prop_simpl_new                    false
% 3.69/0.99  --res_prop_simpl_given                  true
% 3.69/0.99  --res_passive_queue_type                priority_queues
% 3.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.99  --res_passive_queues_freq               [15;5]
% 3.69/0.99  --res_forward_subs                      full
% 3.69/0.99  --res_backward_subs                     full
% 3.69/0.99  --res_forward_subs_resolution           true
% 3.69/0.99  --res_backward_subs_resolution          true
% 3.69/0.99  --res_orphan_elimination                true
% 3.69/0.99  --res_time_limit                        2.
% 3.69/0.99  --res_out_proof                         true
% 3.69/0.99  
% 3.69/0.99  ------ Superposition Options
% 3.69/0.99  
% 3.69/0.99  --superposition_flag                    true
% 3.69/0.99  --sup_passive_queue_type                priority_queues
% 3.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.99  --demod_completeness_check              fast
% 3.69/0.99  --demod_use_ground                      true
% 3.69/0.99  --sup_to_prop_solver                    passive
% 3.69/0.99  --sup_prop_simpl_new                    true
% 3.69/0.99  --sup_prop_simpl_given                  true
% 3.69/0.99  --sup_fun_splitting                     true
% 3.69/0.99  --sup_smt_interval                      50000
% 3.69/0.99  
% 3.69/0.99  ------ Superposition Simplification Setup
% 3.69/0.99  
% 3.69/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.69/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.69/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.69/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.69/0.99  --sup_immed_triv                        [TrivRules]
% 3.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_immed_bw_main                     []
% 3.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_input_bw                          []
% 3.69/0.99  
% 3.69/0.99  ------ Combination Options
% 3.69/0.99  
% 3.69/0.99  --comb_res_mult                         3
% 3.69/0.99  --comb_sup_mult                         2
% 3.69/0.99  --comb_inst_mult                        10
% 3.69/0.99  
% 3.69/0.99  ------ Debug Options
% 3.69/0.99  
% 3.69/0.99  --dbg_backtrace                         false
% 3.69/0.99  --dbg_dump_prop_clauses                 false
% 3.69/0.99  --dbg_dump_prop_clauses_file            -
% 3.69/0.99  --dbg_out_stat                          false
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 26
% 3.69/0.99  conjectures                             1
% 3.69/0.99  EPR                                     3
% 3.69/0.99  Horn                                    24
% 3.69/0.99  unary                                   5
% 3.69/0.99  binary                                  15
% 3.69/0.99  lits                                    53
% 3.69/0.99  lits eq                                 16
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          1
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Schedule dynamic 5 is on 
% 3.69/0.99  
% 3.69/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  ------ Input Options
% 3.69/0.99  
% 3.69/0.99  --out_options                           all
% 3.69/0.99  --tptp_safe_out                         true
% 3.69/0.99  --problem_path                          ""
% 3.69/0.99  --include_path                          ""
% 3.69/0.99  --clausifier                            res/vclausify_rel
% 3.69/0.99  --clausifier_options                    ""
% 3.69/0.99  --stdin                                 false
% 3.69/0.99  --stats_out                             all
% 3.69/0.99  
% 3.69/0.99  ------ General Options
% 3.69/0.99  
% 3.69/0.99  --fof                                   false
% 3.69/0.99  --time_out_real                         305.
% 3.69/0.99  --time_out_virtual                      -1.
% 3.69/0.99  --symbol_type_check                     false
% 3.69/0.99  --clausify_out                          false
% 3.69/0.99  --sig_cnt_out                           false
% 3.69/0.99  --trig_cnt_out                          false
% 3.69/0.99  --trig_cnt_out_tolerance                1.
% 3.69/0.99  --trig_cnt_out_sk_spl                   false
% 3.69/0.99  --abstr_cl_out                          false
% 3.69/0.99  
% 3.69/0.99  ------ Global Options
% 3.69/0.99  
% 3.69/0.99  --schedule                              default
% 3.69/0.99  --add_important_lit                     false
% 3.69/0.99  --prop_solver_per_cl                    1000
% 3.69/0.99  --min_unsat_core                        false
% 3.69/0.99  --soft_assumptions                      false
% 3.69/0.99  --soft_lemma_size                       3
% 3.69/0.99  --prop_impl_unit_size                   0
% 3.69/0.99  --prop_impl_unit                        []
% 3.69/0.99  --share_sel_clauses                     true
% 3.69/0.99  --reset_solvers                         false
% 3.69/0.99  --bc_imp_inh                            [conj_cone]
% 3.69/0.99  --conj_cone_tolerance                   3.
% 3.69/0.99  --extra_neg_conj                        none
% 3.69/0.99  --large_theory_mode                     true
% 3.69/0.99  --prolific_symb_bound                   200
% 3.69/0.99  --lt_threshold                          2000
% 3.69/0.99  --clause_weak_htbl                      true
% 3.69/0.99  --gc_record_bc_elim                     false
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing Options
% 3.69/0.99  
% 3.69/0.99  --preprocessing_flag                    true
% 3.69/0.99  --time_out_prep_mult                    0.1
% 3.69/0.99  --splitting_mode                        input
% 3.69/0.99  --splitting_grd                         true
% 3.69/0.99  --splitting_cvd                         false
% 3.69/0.99  --splitting_cvd_svl                     false
% 3.69/0.99  --splitting_nvd                         32
% 3.69/0.99  --sub_typing                            true
% 3.69/0.99  --prep_gs_sim                           true
% 3.69/0.99  --prep_unflatten                        true
% 3.69/0.99  --prep_res_sim                          true
% 3.69/0.99  --prep_upred                            true
% 3.69/0.99  --prep_sem_filter                       exhaustive
% 3.69/0.99  --prep_sem_filter_out                   false
% 3.69/0.99  --pred_elim                             true
% 3.69/0.99  --res_sim_input                         true
% 3.69/0.99  --eq_ax_congr_red                       true
% 3.69/0.99  --pure_diseq_elim                       true
% 3.69/0.99  --brand_transform                       false
% 3.69/0.99  --non_eq_to_eq                          false
% 3.69/0.99  --prep_def_merge                        true
% 3.69/0.99  --prep_def_merge_prop_impl              false
% 3.69/0.99  --prep_def_merge_mbd                    true
% 3.69/0.99  --prep_def_merge_tr_red                 false
% 3.69/0.99  --prep_def_merge_tr_cl                  false
% 3.69/0.99  --smt_preprocessing                     true
% 3.69/0.99  --smt_ac_axioms                         fast
% 3.69/0.99  --preprocessed_out                      false
% 3.69/0.99  --preprocessed_stats                    false
% 3.69/0.99  
% 3.69/0.99  ------ Abstraction refinement Options
% 3.69/0.99  
% 3.69/0.99  --abstr_ref                             []
% 3.69/0.99  --abstr_ref_prep                        false
% 3.69/0.99  --abstr_ref_until_sat                   false
% 3.69/0.99  --abstr_ref_sig_restrict                funpre
% 3.69/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.69/0.99  --abstr_ref_under                       []
% 3.69/0.99  
% 3.69/0.99  ------ SAT Options
% 3.69/0.99  
% 3.69/0.99  --sat_mode                              false
% 3.69/0.99  --sat_fm_restart_options                ""
% 3.69/0.99  --sat_gr_def                            false
% 3.69/0.99  --sat_epr_types                         true
% 3.69/0.99  --sat_non_cyclic_types                  false
% 3.69/0.99  --sat_finite_models                     false
% 3.69/0.99  --sat_fm_lemmas                         false
% 3.69/0.99  --sat_fm_prep                           false
% 3.69/0.99  --sat_fm_uc_incr                        true
% 3.69/0.99  --sat_out_model                         small
% 3.69/0.99  --sat_out_clauses                       false
% 3.69/0.99  
% 3.69/0.99  ------ QBF Options
% 3.69/0.99  
% 3.69/0.99  --qbf_mode                              false
% 3.69/0.99  --qbf_elim_univ                         false
% 3.69/0.99  --qbf_dom_inst                          none
% 3.69/0.99  --qbf_dom_pre_inst                      false
% 3.69/0.99  --qbf_sk_in                             false
% 3.69/0.99  --qbf_pred_elim                         true
% 3.69/0.99  --qbf_split                             512
% 3.69/0.99  
% 3.69/0.99  ------ BMC1 Options
% 3.69/0.99  
% 3.69/0.99  --bmc1_incremental                      false
% 3.69/0.99  --bmc1_axioms                           reachable_all
% 3.69/0.99  --bmc1_min_bound                        0
% 3.69/0.99  --bmc1_max_bound                        -1
% 3.69/0.99  --bmc1_max_bound_default                -1
% 3.69/0.99  --bmc1_symbol_reachability              true
% 3.69/0.99  --bmc1_property_lemmas                  false
% 3.69/0.99  --bmc1_k_induction                      false
% 3.69/0.99  --bmc1_non_equiv_states                 false
% 3.69/0.99  --bmc1_deadlock                         false
% 3.69/0.99  --bmc1_ucm                              false
% 3.69/0.99  --bmc1_add_unsat_core                   none
% 3.69/0.99  --bmc1_unsat_core_children              false
% 3.69/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.69/0.99  --bmc1_out_stat                         full
% 3.69/0.99  --bmc1_ground_init                      false
% 3.69/0.99  --bmc1_pre_inst_next_state              false
% 3.69/0.99  --bmc1_pre_inst_state                   false
% 3.69/0.99  --bmc1_pre_inst_reach_state             false
% 3.69/0.99  --bmc1_out_unsat_core                   false
% 3.69/0.99  --bmc1_aig_witness_out                  false
% 3.69/0.99  --bmc1_verbose                          false
% 3.69/0.99  --bmc1_dump_clauses_tptp                false
% 3.69/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.69/0.99  --bmc1_dump_file                        -
% 3.69/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.69/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.69/0.99  --bmc1_ucm_extend_mode                  1
% 3.69/0.99  --bmc1_ucm_init_mode                    2
% 3.69/0.99  --bmc1_ucm_cone_mode                    none
% 3.69/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.69/0.99  --bmc1_ucm_relax_model                  4
% 3.69/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.69/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.69/0.99  --bmc1_ucm_layered_model                none
% 3.69/0.99  --bmc1_ucm_max_lemma_size               10
% 3.69/0.99  
% 3.69/0.99  ------ AIG Options
% 3.69/0.99  
% 3.69/0.99  --aig_mode                              false
% 3.69/0.99  
% 3.69/0.99  ------ Instantiation Options
% 3.69/0.99  
% 3.69/0.99  --instantiation_flag                    true
% 3.69/0.99  --inst_sos_flag                         true
% 3.69/0.99  --inst_sos_phase                        true
% 3.69/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.69/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.69/0.99  --inst_lit_sel_side                     none
% 3.69/0.99  --inst_solver_per_active                1400
% 3.69/0.99  --inst_solver_calls_frac                1.
% 3.69/0.99  --inst_passive_queue_type               priority_queues
% 3.69/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.69/0.99  --inst_passive_queues_freq              [25;2]
% 3.69/0.99  --inst_dismatching                      true
% 3.69/0.99  --inst_eager_unprocessed_to_passive     true
% 3.69/0.99  --inst_prop_sim_given                   true
% 3.69/0.99  --inst_prop_sim_new                     false
% 3.69/0.99  --inst_subs_new                         false
% 3.69/0.99  --inst_eq_res_simp                      false
% 3.69/0.99  --inst_subs_given                       false
% 3.69/0.99  --inst_orphan_elimination               true
% 3.69/0.99  --inst_learning_loop_flag               true
% 3.69/0.99  --inst_learning_start                   3000
% 3.69/0.99  --inst_learning_factor                  2
% 3.69/0.99  --inst_start_prop_sim_after_learn       3
% 3.69/0.99  --inst_sel_renew                        solver
% 3.69/0.99  --inst_lit_activity_flag                true
% 3.69/0.99  --inst_restr_to_given                   false
% 3.69/0.99  --inst_activity_threshold               500
% 3.69/0.99  --inst_out_proof                        true
% 3.69/0.99  
% 3.69/0.99  ------ Resolution Options
% 3.69/0.99  
% 3.69/0.99  --resolution_flag                       false
% 3.69/0.99  --res_lit_sel                           adaptive
% 3.69/0.99  --res_lit_sel_side                      none
% 3.69/0.99  --res_ordering                          kbo
% 3.69/0.99  --res_to_prop_solver                    active
% 3.69/0.99  --res_prop_simpl_new                    false
% 3.69/0.99  --res_prop_simpl_given                  true
% 3.69/0.99  --res_passive_queue_type                priority_queues
% 3.69/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.69/0.99  --res_passive_queues_freq               [15;5]
% 3.69/0.99  --res_forward_subs                      full
% 3.69/0.99  --res_backward_subs                     full
% 3.69/0.99  --res_forward_subs_resolution           true
% 3.69/0.99  --res_backward_subs_resolution          true
% 3.69/0.99  --res_orphan_elimination                true
% 3.69/0.99  --res_time_limit                        2.
% 3.69/0.99  --res_out_proof                         true
% 3.69/0.99  
% 3.69/0.99  ------ Superposition Options
% 3.69/0.99  
% 3.69/0.99  --superposition_flag                    true
% 3.69/0.99  --sup_passive_queue_type                priority_queues
% 3.69/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.69/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.69/0.99  --demod_completeness_check              fast
% 3.69/0.99  --demod_use_ground                      true
% 3.69/0.99  --sup_to_prop_solver                    passive
% 3.69/0.99  --sup_prop_simpl_new                    true
% 3.69/0.99  --sup_prop_simpl_given                  true
% 3.69/0.99  --sup_fun_splitting                     true
% 3.69/0.99  --sup_smt_interval                      50000
% 3.69/0.99  
% 3.69/0.99  ------ Superposition Simplification Setup
% 3.69/0.99  
% 3.69/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.69/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.69/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.69/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.69/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.69/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.69/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.69/0.99  --sup_immed_triv                        [TrivRules]
% 3.69/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_immed_bw_main                     []
% 3.69/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.69/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.69/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.69/0.99  --sup_input_bw                          []
% 3.69/0.99  
% 3.69/0.99  ------ Combination Options
% 3.69/0.99  
% 3.69/0.99  --comb_res_mult                         3
% 3.69/0.99  --comb_sup_mult                         2
% 3.69/0.99  --comb_inst_mult                        10
% 3.69/0.99  
% 3.69/0.99  ------ Debug Options
% 3.69/0.99  
% 3.69/0.99  --dbg_backtrace                         false
% 3.69/0.99  --dbg_dump_prop_clauses                 false
% 3.69/0.99  --dbg_dump_prop_clauses_file            -
% 3.69/0.99  --dbg_out_stat                          false
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status Theorem for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f13,axiom,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f36,plain,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f13])).
% 3.69/0.99  
% 3.69/0.99  fof(f89,plain,(
% 3.69/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f36])).
% 3.69/0.99  
% 3.69/0.99  fof(f24,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f48,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f24])).
% 3.69/0.99  
% 3.69/0.99  fof(f65,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f48])).
% 3.69/0.99  
% 3.69/0.99  fof(f100,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f65])).
% 3.69/0.99  
% 3.69/0.99  fof(f27,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f51,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f27])).
% 3.69/0.99  
% 3.69/0.99  fof(f52,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f51])).
% 3.69/0.99  
% 3.69/0.99  fof(f106,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f52])).
% 3.69/0.99  
% 3.69/0.99  fof(f29,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f55,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f29])).
% 3.69/0.99  
% 3.69/0.99  fof(f56,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f55])).
% 3.69/0.99  
% 3.69/0.99  fof(f108,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f56])).
% 3.69/0.99  
% 3.69/0.99  fof(f30,conjecture,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f31,negated_conjecture,(
% 3.69/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 3.69/0.99    inference(negated_conjecture,[],[f30])).
% 3.69/0.99  
% 3.69/0.99  fof(f57,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f31])).
% 3.69/0.99  
% 3.69/0.99  fof(f58,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f57])).
% 3.69/0.99  
% 3.69/0.99  fof(f68,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f58])).
% 3.69/0.99  
% 3.69/0.99  fof(f69,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f68])).
% 3.69/0.99  
% 3.69/0.99  fof(f71,plain,(
% 3.69/0.99    ( ! [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k2_tops_1(X0,sK2) != sK2 | ~v3_tops_1(sK2,X0)) & (k2_tops_1(X0,sK2) = sK2 | v3_tops_1(sK2,X0)) & v4_pre_topc(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f70,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK1,X1) != X1 | ~v3_tops_1(X1,sK1)) & (k2_tops_1(sK1,X1) = X1 | v3_tops_1(X1,sK1)) & v4_pre_topc(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f72,plain,(
% 3.69/0.99    ((k2_tops_1(sK1,sK2) != sK2 | ~v3_tops_1(sK2,sK1)) & (k2_tops_1(sK1,sK2) = sK2 | v3_tops_1(sK2,sK1)) & v4_pre_topc(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f69,f71,f70])).
% 3.69/0.99  
% 3.69/0.99  fof(f111,plain,(
% 3.69/0.99    v4_pre_topc(sK2,sK1)),
% 3.69/0.99    inference(cnf_transformation,[],[f72])).
% 3.69/0.99  
% 3.69/0.99  fof(f109,plain,(
% 3.69/0.99    l1_pre_topc(sK1)),
% 3.69/0.99    inference(cnf_transformation,[],[f72])).
% 3.69/0.99  
% 3.69/0.99  fof(f110,plain,(
% 3.69/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.69/0.99    inference(cnf_transformation,[],[f72])).
% 3.69/0.99  
% 3.69/0.99  fof(f26,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f50,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f26])).
% 3.69/0.99  
% 3.69/0.99  fof(f67,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f50])).
% 3.69/0.99  
% 3.69/0.99  fof(f105,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f67])).
% 3.69/0.99  
% 3.69/0.99  fof(f2,axiom,(
% 3.69/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f63,plain,(
% 3.69/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.69/0.99    inference(nnf_transformation,[],[f2])).
% 3.69/0.99  
% 3.69/0.99  fof(f64,plain,(
% 3.69/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.69/0.99    inference(flattening,[],[f63])).
% 3.69/0.99  
% 3.69/0.99  fof(f76,plain,(
% 3.69/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.69/0.99    inference(cnf_transformation,[],[f64])).
% 3.69/0.99  
% 3.69/0.99  fof(f126,plain,(
% 3.69/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.69/0.99    inference(equality_resolution,[],[f76])).
% 3.69/0.99  
% 3.69/0.99  fof(f78,plain,(
% 3.69/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f64])).
% 3.69/0.99  
% 3.69/0.99  fof(f112,plain,(
% 3.69/0.99    k2_tops_1(sK1,sK2) = sK2 | v3_tops_1(sK2,sK1)),
% 3.69/0.99    inference(cnf_transformation,[],[f72])).
% 3.69/0.99  
% 3.69/0.99  fof(f20,axiom,(
% 3.69/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f42,plain,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f20])).
% 3.69/0.99  
% 3.69/0.99  fof(f43,plain,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(flattening,[],[f42])).
% 3.69/1.00  
% 3.69/1.00  fof(f96,plain,(
% 3.69/1.00    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f43])).
% 3.69/1.00  
% 3.69/1.00  fof(f14,axiom,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f37,plain,(
% 3.69/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f14])).
% 3.69/1.00  
% 3.69/1.00  fof(f90,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f37])).
% 3.69/1.00  
% 3.69/1.00  fof(f22,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1)))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f46,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f22])).
% 3.69/1.00  
% 3.69/1.00  fof(f98,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f46])).
% 3.69/1.00  
% 3.69/1.00  fof(f25,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f49,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f25])).
% 3.69/1.00  
% 3.69/1.00  fof(f66,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(nnf_transformation,[],[f49])).
% 3.69/1.00  
% 3.69/1.00  fof(f102,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f66])).
% 3.69/1.00  
% 3.69/1.00  fof(f28,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f53,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f28])).
% 3.69/1.00  
% 3.69/1.00  fof(f54,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(flattening,[],[f53])).
% 3.69/1.00  
% 3.69/1.00  fof(f107,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f54])).
% 3.69/1.00  
% 3.69/1.00  fof(f17,axiom,(
% 3.69/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f93,plain,(
% 3.69/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f17])).
% 3.69/1.00  
% 3.69/1.00  fof(f12,axiom,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f35,plain,(
% 3.69/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f12])).
% 3.69/1.00  
% 3.69/1.00  fof(f88,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f35])).
% 3.69/1.00  
% 3.69/1.00  fof(f3,axiom,(
% 3.69/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f79,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f3])).
% 3.69/1.00  
% 3.69/1.00  fof(f18,axiom,(
% 3.69/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f94,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f18])).
% 3.69/1.00  
% 3.69/1.00  fof(f6,axiom,(
% 3.69/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f82,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f6])).
% 3.69/1.00  
% 3.69/1.00  fof(f7,axiom,(
% 3.69/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f83,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f7])).
% 3.69/1.00  
% 3.69/1.00  fof(f8,axiom,(
% 3.69/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f84,plain,(
% 3.69/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f8])).
% 3.69/1.00  
% 3.69/1.00  fof(f9,axiom,(
% 3.69/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f85,plain,(
% 3.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f9])).
% 3.69/1.00  
% 3.69/1.00  fof(f10,axiom,(
% 3.69/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f86,plain,(
% 3.69/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f10])).
% 3.69/1.00  
% 3.69/1.00  fof(f11,axiom,(
% 3.69/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f87,plain,(
% 3.69/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f11])).
% 3.69/1.00  
% 3.69/1.00  fof(f114,plain,(
% 3.69/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f86,f87])).
% 3.69/1.00  
% 3.69/1.00  fof(f115,plain,(
% 3.69/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f85,f114])).
% 3.69/1.00  
% 3.69/1.00  fof(f116,plain,(
% 3.69/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f84,f115])).
% 3.69/1.00  
% 3.69/1.00  fof(f117,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f83,f116])).
% 3.69/1.00  
% 3.69/1.00  fof(f118,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f82,f117])).
% 3.69/1.00  
% 3.69/1.00  fof(f119,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.69/1.00    inference(definition_unfolding,[],[f94,f118])).
% 3.69/1.00  
% 3.69/1.00  fof(f120,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.69/1.00    inference(definition_unfolding,[],[f79,f119])).
% 3.69/1.00  
% 3.69/1.00  fof(f123,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(definition_unfolding,[],[f88,f120])).
% 3.69/1.00  
% 3.69/1.00  fof(f5,axiom,(
% 3.69/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f81,plain,(
% 3.69/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.69/1.00    inference(cnf_transformation,[],[f5])).
% 3.69/1.00  
% 3.69/1.00  fof(f122,plain,(
% 3.69/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 3.69/1.00    inference(definition_unfolding,[],[f81,f120])).
% 3.69/1.00  
% 3.69/1.00  fof(f23,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1)))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f47,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f23])).
% 3.69/1.00  
% 3.69/1.00  fof(f99,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f47])).
% 3.69/1.00  
% 3.69/1.00  fof(f21,axiom,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f32,plain,(
% 3.69/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 3.69/1.00    inference(pure_predicate_removal,[],[f21])).
% 3.69/1.00  
% 3.69/1.00  fof(f44,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(ennf_transformation,[],[f32])).
% 3.69/1.00  
% 3.69/1.00  fof(f45,plain,(
% 3.69/1.00    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/1.00    inference(flattening,[],[f44])).
% 3.69/1.00  
% 3.69/1.00  fof(f97,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f45])).
% 3.69/1.00  
% 3.69/1.00  fof(f16,axiom,(
% 3.69/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f39,plain,(
% 3.69/1.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f16])).
% 3.69/1.00  
% 3.69/1.00  fof(f92,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f39])).
% 3.69/1.00  
% 3.69/1.00  fof(f124,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(definition_unfolding,[],[f92,f119])).
% 3.69/1.00  
% 3.69/1.00  fof(f1,axiom,(
% 3.69/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f33,plain,(
% 3.69/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f1])).
% 3.69/1.00  
% 3.69/1.00  fof(f59,plain,(
% 3.69/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/1.00    inference(nnf_transformation,[],[f33])).
% 3.69/1.00  
% 3.69/1.00  fof(f60,plain,(
% 3.69/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/1.00    inference(rectify,[],[f59])).
% 3.69/1.00  
% 3.69/1.00  fof(f61,plain,(
% 3.69/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.69/1.00    introduced(choice_axiom,[])).
% 3.69/1.00  
% 3.69/1.00  fof(f62,plain,(
% 3.69/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.69/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f60,f61])).
% 3.69/1.00  
% 3.69/1.00  fof(f74,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f62])).
% 3.69/1.00  
% 3.69/1.00  fof(f15,axiom,(
% 3.69/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f38,plain,(
% 3.69/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/1.00    inference(ennf_transformation,[],[f15])).
% 3.69/1.00  
% 3.69/1.00  fof(f91,plain,(
% 3.69/1.00    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/1.00    inference(cnf_transformation,[],[f38])).
% 3.69/1.00  
% 3.69/1.00  fof(f75,plain,(
% 3.69/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f62])).
% 3.69/1.00  
% 3.69/1.00  fof(f4,axiom,(
% 3.69/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.69/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/1.00  
% 3.69/1.00  fof(f34,plain,(
% 3.69/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.69/1.00    inference(ennf_transformation,[],[f4])).
% 3.69/1.00  
% 3.69/1.00  fof(f80,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f34])).
% 3.69/1.00  
% 3.69/1.00  fof(f121,plain,(
% 3.69/1.00    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.69/1.00    inference(definition_unfolding,[],[f80,f119])).
% 3.69/1.00  
% 3.69/1.00  fof(f113,plain,(
% 3.69/1.00    k2_tops_1(sK1,sK2) != sK2 | ~v3_tops_1(sK2,sK1)),
% 3.69/1.00    inference(cnf_transformation,[],[f72])).
% 3.69/1.00  
% 3.69/1.00  fof(f103,plain,(
% 3.69/1.00    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/1.00    inference(cnf_transformation,[],[f66])).
% 3.69/1.00  
% 3.69/1.00  cnf(c_9,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1815,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.69/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_20,plain,
% 3.69/1.00      ( ~ v1_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,X0) = k2_struct_0(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_25,plain,
% 3.69/1.00      ( ~ v3_tops_1(X0,X1)
% 3.69/1.00      | v1_tops_1(k3_subset_1(u1_struct_0(X1),X0),X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_441,plain,
% 3.69/1.00      ( ~ v3_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X3)
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | X1 != X3
% 3.69/1.00      | k2_pre_topc(X3,X2) = k2_struct_0(X3)
% 3.69/1.00      | k3_subset_1(u1_struct_0(X1),X0) != X2 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_442,plain,
% 3.69/1.00      ( ~ v3_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ m1_subset_1(k3_subset_1(u1_struct_0(X1),X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_441]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_456,plain,
% 3.69/1.00      ( ~ v3_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1) ),
% 3.69/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_442,c_9]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_27,plain,
% 3.69/1.00      ( v3_tops_1(X0,X1)
% 3.69/1.00      | ~ v2_tops_1(X0,X1)
% 3.69/1.00      | ~ v4_pre_topc(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_30,negated_conjecture,
% 3.69/1.00      ( v4_pre_topc(sK2,sK1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_414,plain,
% 3.69/1.00      ( v3_tops_1(X0,X1)
% 3.69/1.00      | ~ v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_27,c_30]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_415,plain,
% 3.69/1.00      ( v3_tops_1(sK2,sK1)
% 3.69/1.00      | ~ v2_tops_1(sK2,sK1)
% 3.69/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ l1_pre_topc(sK1) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_32,negated_conjecture,
% 3.69/1.00      ( l1_pre_topc(sK1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f109]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_31,negated_conjecture,
% 3.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.69/1.00      inference(cnf_transformation,[],[f110]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_417,plain,
% 3.69/1.00      ( v3_tops_1(sK2,sK1) | ~ v2_tops_1(sK2,sK1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_415,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_479,plain,
% 3.69/1.00      ( ~ v2_tops_1(sK2,sK1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_456,c_417]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_480,plain,
% 3.69/1.00      ( ~ v2_tops_1(sK2,sK1)
% 3.69/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ l1_pre_topc(sK1)
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_479]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_482,plain,
% 3.69/1.00      ( ~ v2_tops_1(sK2,sK1)
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_480,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_23,plain,
% 3.69/1.00      ( v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f105]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_546,plain,
% 3.69/1.00      ( v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ r1_tarski(X0,k2_tops_1(X1,X0))
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_547,plain,
% 3.69/1.00      ( v2_tops_1(X0,sK1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ r1_tarski(X0,k2_tops_1(sK1,X0)) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_546]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_720,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ r1_tarski(X0,k2_tops_1(sK1,X0))
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != sK1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_482,c_547]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_721,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_720]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_723,plain,
% 3.69/1.00      ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_721,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1802,plain,
% 3.69/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1)
% 3.69/1.00      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_5,plain,
% 3.69/1.00      ( r1_tarski(X0,X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f126]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_101,plain,
% 3.69/1.00      ( r1_tarski(sK2,sK2) ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_105,plain,
% 3.69/1.00      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_29,negated_conjecture,
% 3.69/1.00      ( v3_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(cnf_transformation,[],[f112]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_248,plain,
% 3.69/1.00      ( v3_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_29]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_493,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_struct_0(X1)
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_456,c_248]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_494,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ l1_pre_topc(sK1)
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_493]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_496,plain,
% 3.69/1.00      ( k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_494,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1235,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.69/1.00      theory(equality) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1862,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1)
% 3.69/1.00      | r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k2_tops_1(sK1,sK2) != X1
% 3.69/1.00      | sK2 != X0 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1235]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1864,plain,
% 3.69/1.00      ( r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | ~ r1_tarski(sK2,sK2)
% 3.69/1.00      | k2_tops_1(sK1,sK2) != sK2
% 3.69/1.00      | sK2 != sK2 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_1862]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2039,plain,
% 3.69/1.00      ( k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2)) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1802,c_31,c_101,c_105,c_496,c_721,c_1864]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_15,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_615,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_616,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_615]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1806,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.69/1.00      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2043,plain,
% 3.69/1.00      ( m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.69/1.00      | m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_2039,c_1806]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_3377,plain,
% 3.69/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 3.69/1.00      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1815,c_2043]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_34,plain,
% 3.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12228,plain,
% 3.69/1.00      ( m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_3377,c_34]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_10,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1814,plain,
% 3.69/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.69/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12233,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1))) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_12228,c_1814]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1809,plain,
% 3.69/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_17,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_603,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k1_tops_1(X1,X0)
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_604,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_603]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1807,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k1_tops_1(sK1,X0)
% 3.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1891,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k1_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1809,c_1807]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2042,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = k1_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(demodulation,[status(thm)],[c_2039,c_1891]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_22,plain,
% 3.69/1.00      ( ~ v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_561,plain,
% 3.69/1.00      ( ~ v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | k1_tops_1(X1,X0) = k1_xboole_0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_562,plain,
% 3.69/1.00      ( ~ v2_tops_1(X0,sK1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_561]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_669,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ r1_tarski(X0,k2_tops_1(sK1,X0))
% 3.69/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_547,c_562]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_671,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(instantiation,[status(thm)],[c_669]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1097,plain,
% 3.69/1.00      ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_31,c_671]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1799,plain,
% 3.69/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 3.69/1.00      | r1_tarski(sK2,k2_tops_1(sK1,sK2)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1097]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_26,plain,
% 3.69/1.00      ( ~ v3_tops_1(X0,X1)
% 3.69/1.00      | v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_506,plain,
% 3.69/1.00      ( v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_248]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_507,plain,
% 3.69/1.00      ( v2_tops_1(sK2,sK1)
% 3.69/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ l1_pre_topc(sK1)
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_506]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_509,plain,
% 3.69/1.00      ( v2_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_507,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_684,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | k1_tops_1(sK1,X0) = k1_xboole_0
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != sK1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_509,c_562]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_685,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k2_tops_1(sK1,sK2) = sK2
% 3.69/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_684]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_687,plain,
% 3.69/1.00      ( k2_tops_1(sK1,sK2) = sK2 | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_685,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_867,plain,
% 3.69/1.00      ( ~ r1_tarski(sK2,k2_tops_1(sK1,sK2))
% 3.69/1.00      | k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_31,c_671]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2119,plain,
% 3.69/1.00      ( k1_tops_1(sK1,sK2) = k1_xboole_0 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_1799,c_101,c_105,c_687,c_867,c_1864]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2256,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k2_struct_0(sK1)) = k1_xboole_0 ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_2042,c_2042,c_2119]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12330,plain,
% 3.69/1.00      ( k3_subset_1(u1_struct_0(sK1),k1_xboole_0) = k2_struct_0(sK1) ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_12233,c_2256]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_13,plain,
% 3.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.69/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1811,plain,
% 3.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))) = k3_subset_1(X1,X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f123]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1816,plain,
% 3.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k3_subset_1(X0,X1)
% 3.69/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4310,plain,
% 3.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = k3_subset_1(X0,k1_xboole_0) ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1811,c_1816]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_7,plain,
% 3.69/1.00      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f122]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4314,plain,
% 3.69/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_4310,c_7]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12331,plain,
% 3.69/1.00      ( k2_struct_0(sK1) = u1_struct_0(sK1) ),
% 3.69/1.00      inference(demodulation,[status(thm)],[c_12330,c_4314]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_18,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_591,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X0))) = k2_tops_1(X1,X0)
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_592,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k2_tops_1(sK1,X0) ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1808,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),X0))) = k2_tops_1(sK1,X0)
% 3.69/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1944,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k2_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1809,c_1808]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_16,plain,
% 3.69/1.00      ( ~ v4_pre_topc(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_428,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k2_pre_topc(X1,X0) = X0
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_30]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_429,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | ~ l1_pre_topc(sK1)
% 3.69/1.00      | k2_pre_topc(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_428]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_431,plain,
% 3.69/1.00      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_429,c_32,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1946,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK2))) = k2_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_1944,c_431]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_2041,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),sK2,k2_struct_0(sK1)) = k2_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(demodulation,[status(thm)],[c_2039,c_1946]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12562,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),sK2,u1_struct_0(sK1)) = k2_tops_1(sK1,sK2) ),
% 3.69/1.00      inference(demodulation,[status(thm)],[c_12331,c_2041]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4324,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top
% 3.69/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4314,c_1815]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_80,plain,
% 3.69/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8848,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_4324,c_80]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 3.69/1.00      inference(cnf_transformation,[],[f124]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1812,plain,
% 3.69/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X2,X0,X1)
% 3.69/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_8858,plain,
% 3.69/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k9_subset_1(X1,X0,X1) ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_8848,c_1812]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1821,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.69/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_11,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/1.00      | ~ r2_hidden(X2,X0)
% 3.69/1.00      | r2_hidden(X2,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1813,plain,
% 3.69/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.69/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.69/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4199,plain,
% 3.69/1.00      ( r2_hidden(X0,u1_struct_0(sK1)) = iProver_top
% 3.69/1.00      | r2_hidden(X0,sK2) != iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1809,c_1813]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_0,plain,
% 3.69/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.69/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1822,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.69/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4412,plain,
% 3.69/1.00      ( r2_hidden(sK0(X0,u1_struct_0(sK1)),sK2) != iProver_top
% 3.69/1.00      | r1_tarski(X0,u1_struct_0(sK1)) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4199,c_1822]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4600,plain,
% 3.69/1.00      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_1821,c_4412]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_6,plain,
% 3.69/1.00      ( ~ r1_tarski(X0,X1)
% 3.69/1.00      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_1817,plain,
% 3.69/1.00      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
% 3.69/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.69/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_4918,plain,
% 3.69/1.00      ( k1_setfam_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,u1_struct_0(sK1))) = sK2 ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_4600,c_1817]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_10723,plain,
% 3.69/1.00      ( k9_subset_1(u1_struct_0(sK1),sK2,u1_struct_0(sK1)) = sK2 ),
% 3.69/1.00      inference(superposition,[status(thm)],[c_8858,c_4918]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_12565,plain,
% 3.69/1.00      ( k2_tops_1(sK1,sK2) = sK2 ),
% 3.69/1.00      inference(light_normalisation,[status(thm)],[c_12562,c_10723]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_28,negated_conjecture,
% 3.69/1.00      ( ~ v3_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) != sK2 ),
% 3.69/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_246,plain,
% 3.69/1.00      ( ~ v3_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) != sK2 ),
% 3.69/1.00      inference(prop_impl,[status(thm)],[c_28]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_469,plain,
% 3.69/1.00      ( ~ v2_tops_1(sK2,sK1) | k2_tops_1(sK1,sK2) != sK2 ),
% 3.69/1.00      inference(resolution,[status(thm)],[c_417,c_246]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_21,plain,
% 3.69/1.00      ( v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | ~ l1_pre_topc(X1)
% 3.69/1.00      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.69/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_576,plain,
% 3.69/1.00      ( v2_tops_1(X0,X1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/1.00      | k1_tops_1(X1,X0) != k1_xboole_0
% 3.69/1.00      | sK1 != X1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_577,plain,
% 3.69/1.00      ( v2_tops_1(X0,sK1)
% 3.69/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_576]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_734,plain,
% 3.69/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k2_tops_1(sK1,sK2) != sK2
% 3.69/1.00      | k1_tops_1(sK1,X0) != k1_xboole_0
% 3.69/1.00      | sK2 != X0
% 3.69/1.00      | sK1 != sK1 ),
% 3.69/1.00      inference(resolution_lifted,[status(thm)],[c_469,c_577]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_735,plain,
% 3.69/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.69/1.00      | k2_tops_1(sK1,sK2) != sK2
% 3.69/1.00      | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 3.69/1.00      inference(unflattening,[status(thm)],[c_734]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(c_737,plain,
% 3.69/1.00      ( k2_tops_1(sK1,sK2) != sK2 | k1_tops_1(sK1,sK2) != k1_xboole_0 ),
% 3.69/1.00      inference(global_propositional_subsumption,
% 3.69/1.00                [status(thm)],
% 3.69/1.00                [c_735,c_31]) ).
% 3.69/1.00  
% 3.69/1.00  cnf(contradiction,plain,
% 3.69/1.00      ( $false ),
% 3.69/1.00      inference(minisat,[status(thm)],[c_12565,c_2119,c_737]) ).
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.69/1.00  
% 3.69/1.00  ------                               Statistics
% 3.69/1.00  
% 3.69/1.00  ------ General
% 3.69/1.00  
% 3.69/1.00  abstr_ref_over_cycles:                  0
% 3.69/1.00  abstr_ref_under_cycles:                 0
% 3.69/1.00  gc_basic_clause_elim:                   0
% 3.69/1.00  forced_gc_time:                         0
% 3.69/1.00  parsing_time:                           0.016
% 3.69/1.00  unif_index_cands_time:                  0.
% 3.69/1.00  unif_index_add_time:                    0.
% 3.69/1.00  orderings_time:                         0.
% 3.69/1.00  out_proof_time:                         0.014
% 3.69/1.00  total_time:                             0.459
% 3.69/1.00  num_of_symbols:                         55
% 3.69/1.00  num_of_terms:                           13043
% 3.69/1.00  
% 3.69/1.00  ------ Preprocessing
% 3.69/1.00  
% 3.69/1.00  num_of_splits:                          0
% 3.69/1.00  num_of_split_atoms:                     1
% 3.69/1.00  num_of_reused_defs:                     0
% 3.69/1.00  num_eq_ax_congr_red:                    52
% 3.69/1.00  num_of_sem_filtered_clauses:            1
% 3.69/1.00  num_of_subtypes:                        0
% 3.69/1.00  monotx_restored_types:                  0
% 3.69/1.00  sat_num_of_epr_types:                   0
% 3.69/1.00  sat_num_of_non_cyclic_types:            0
% 3.69/1.00  sat_guarded_non_collapsed_types:        0
% 3.69/1.00  num_pure_diseq_elim:                    0
% 3.69/1.00  simp_replaced_by:                       0
% 3.69/1.00  res_preprocessed:                       169
% 3.69/1.00  prep_upred:                             0
% 3.69/1.00  prep_unflattend:                        27
% 3.69/1.00  smt_new_axioms:                         0
% 3.69/1.00  pred_elim_cands:                        3
% 3.69/1.00  pred_elim:                              5
% 3.69/1.00  pred_elim_cl:                           4
% 3.69/1.00  pred_elim_cycles:                       8
% 3.69/1.00  merged_defs:                            18
% 3.69/1.00  merged_defs_ncl:                        0
% 3.69/1.00  bin_hyper_res:                          20
% 3.69/1.00  prep_cycles:                            5
% 3.69/1.00  pred_elim_time:                         0.008
% 3.69/1.00  splitting_time:                         0.
% 3.69/1.00  sem_filter_time:                        0.
% 3.69/1.00  monotx_time:                            0.
% 3.69/1.00  subtype_inf_time:                       0.
% 3.69/1.00  
% 3.69/1.00  ------ Problem properties
% 3.69/1.00  
% 3.69/1.00  clauses:                                26
% 3.69/1.00  conjectures:                            1
% 3.69/1.00  epr:                                    3
% 3.69/1.00  horn:                                   24
% 3.69/1.00  ground:                                 7
% 3.69/1.00  unary:                                  5
% 3.69/1.00  binary:                                 15
% 3.69/1.00  lits:                                   53
% 3.69/1.00  lits_eq:                                16
% 3.69/1.00  fd_pure:                                0
% 3.69/1.00  fd_pseudo:                              0
% 3.69/1.00  fd_cond:                                0
% 3.69/1.00  fd_pseudo_cond:                         1
% 3.69/1.00  ac_symbols:                             0
% 3.69/1.00  
% 3.69/1.00  ------ Propositional Solver
% 3.69/1.00  
% 3.69/1.00  prop_solver_calls:                      38
% 3.69/1.00  prop_fast_solver_calls:                 1155
% 3.69/1.00  smt_solver_calls:                       0
% 3.69/1.00  smt_fast_solver_calls:                  0
% 3.69/1.00  prop_num_of_clauses:                    5181
% 3.69/1.00  prop_preprocess_simplified:             13246
% 3.69/1.00  prop_fo_subsumed:                       26
% 3.69/1.00  prop_solver_time:                       0.
% 3.69/1.00  smt_solver_time:                        0.
% 3.69/1.00  smt_fast_solver_time:                   0.
% 3.69/1.00  prop_fast_solver_time:                  0.
% 3.69/1.00  prop_unsat_core_time:                   0.
% 3.69/1.00  
% 3.69/1.00  ------ QBF
% 3.69/1.00  
% 3.69/1.00  qbf_q_res:                              0
% 3.69/1.00  qbf_num_tautologies:                    0
% 3.69/1.00  qbf_prep_cycles:                        0
% 3.69/1.00  
% 3.69/1.00  ------ BMC1
% 3.69/1.00  
% 3.69/1.00  bmc1_current_bound:                     -1
% 3.69/1.00  bmc1_last_solved_bound:                 -1
% 3.69/1.00  bmc1_unsat_core_size:                   -1
% 3.69/1.00  bmc1_unsat_core_parents_size:           -1
% 3.69/1.00  bmc1_merge_next_fun:                    0
% 3.69/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.69/1.00  
% 3.69/1.00  ------ Instantiation
% 3.69/1.00  
% 3.69/1.00  inst_num_of_clauses:                    1527
% 3.69/1.00  inst_num_in_passive:                    860
% 3.69/1.00  inst_num_in_active:                     637
% 3.69/1.00  inst_num_in_unprocessed:                30
% 3.69/1.00  inst_num_of_loops:                      760
% 3.69/1.00  inst_num_of_learning_restarts:          0
% 3.69/1.00  inst_num_moves_active_passive:          118
% 3.69/1.00  inst_lit_activity:                      0
% 3.69/1.00  inst_lit_activity_moves:                0
% 3.69/1.00  inst_num_tautologies:                   0
% 3.69/1.00  inst_num_prop_implied:                  0
% 3.69/1.00  inst_num_existing_simplified:           0
% 3.69/1.00  inst_num_eq_res_simplified:             0
% 3.69/1.00  inst_num_child_elim:                    0
% 3.69/1.00  inst_num_of_dismatching_blockings:      776
% 3.69/1.00  inst_num_of_non_proper_insts:           1714
% 3.69/1.00  inst_num_of_duplicates:                 0
% 3.69/1.00  inst_inst_num_from_inst_to_res:         0
% 3.69/1.00  inst_dismatching_checking_time:         0.
% 3.69/1.00  
% 3.69/1.00  ------ Resolution
% 3.69/1.00  
% 3.69/1.00  res_num_of_clauses:                     0
% 3.69/1.00  res_num_in_passive:                     0
% 3.69/1.00  res_num_in_active:                      0
% 3.69/1.00  res_num_of_loops:                       174
% 3.69/1.00  res_forward_subset_subsumed:            119
% 3.69/1.00  res_backward_subset_subsumed:           0
% 3.69/1.00  res_forward_subsumed:                   0
% 3.69/1.00  res_backward_subsumed:                  0
% 3.69/1.00  res_forward_subsumption_resolution:     1
% 3.69/1.00  res_backward_subsumption_resolution:    0
% 3.69/1.00  res_clause_to_clause_subsumption:       2276
% 3.69/1.00  res_orphan_elimination:                 0
% 3.69/1.00  res_tautology_del:                      217
% 3.69/1.00  res_num_eq_res_simplified:              0
% 3.69/1.00  res_num_sel_changes:                    0
% 3.69/1.00  res_moves_from_active_to_pass:          0
% 3.69/1.00  
% 3.69/1.00  ------ Superposition
% 3.69/1.00  
% 3.69/1.00  sup_time_total:                         0.
% 3.69/1.00  sup_time_generating:                    0.
% 3.69/1.00  sup_time_sim_full:                      0.
% 3.69/1.00  sup_time_sim_immed:                     0.
% 3.69/1.00  
% 3.69/1.00  sup_num_of_clauses:                     405
% 3.69/1.00  sup_num_in_active:                      128
% 3.69/1.00  sup_num_in_passive:                     277
% 3.69/1.00  sup_num_of_loops:                       150
% 3.69/1.00  sup_fw_superposition:                   352
% 3.69/1.00  sup_bw_superposition:                   274
% 3.69/1.00  sup_immediate_simplified:               258
% 3.69/1.00  sup_given_eliminated:                   3
% 3.69/1.00  comparisons_done:                       0
% 3.69/1.00  comparisons_avoided:                    0
% 3.69/1.00  
% 3.69/1.00  ------ Simplifications
% 3.69/1.00  
% 3.69/1.00  
% 3.69/1.00  sim_fw_subset_subsumed:                 5
% 3.69/1.00  sim_bw_subset_subsumed:                 1
% 3.69/1.00  sim_fw_subsumed:                        15
% 3.69/1.00  sim_bw_subsumed:                        6
% 3.69/1.00  sim_fw_subsumption_res:                 0
% 3.69/1.00  sim_bw_subsumption_res:                 0
% 3.69/1.00  sim_tautology_del:                      6
% 3.69/1.00  sim_eq_tautology_del:                   60
% 3.69/1.00  sim_eq_res_simp:                        0
% 3.69/1.00  sim_fw_demodulated:                     86
% 3.69/1.00  sim_bw_demodulated:                     94
% 3.69/1.00  sim_light_normalised:                   196
% 3.69/1.00  sim_joinable_taut:                      0
% 3.69/1.00  sim_joinable_simp:                      0
% 3.69/1.00  sim_ac_normalised:                      0
% 3.69/1.00  sim_smt_subsumption:                    0
% 3.69/1.00  
%------------------------------------------------------------------------------
