%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:38 EST 2020

% Result     : Theorem 2.09s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 194 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :   21
%              Number of atoms          :  261 ( 739 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1907,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1898,f921])).

fof(f921,plain,(
    ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f920,f67])).

fof(f67,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    & v3_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f61,f60])).

fof(f60,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
          & v3_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X1] :
        ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0)
        & v3_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      & v3_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f33,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f920,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f919,f68])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f62])).

fof(f919,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f918,f69])).

fof(f69,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f918,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v3_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f804,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).

fof(f804,plain,
    ( ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f803,f68])).

fof(f803,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f792,f67])).

fof(f792,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f703,f203])).

fof(f203,plain,(
    ! [X6,X7] :
      ( r1_tarski(k2_pre_topc(X6,X7),k2_tops_1(X6,k2_pre_topc(X6,X7)))
      | ~ v2_tops_1(k2_pre_topc(X6,X7),X6)
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f199])).

fof(f199,plain,(
    ! [X6,X7] :
      ( ~ v2_tops_1(k2_pre_topc(X6,X7),X6)
      | r1_tarski(k2_pre_topc(X6,X7),k2_tops_1(X6,k2_pre_topc(X6,X7)))
      | ~ l1_pre_topc(X6)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6) ) ),
    inference(resolution,[],[f79,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f703,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
      | ~ r1_tarski(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f702,f238])).

fof(f238,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f237,f67])).

fof(f237,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f233,f68])).

fof(f233,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f81,f70])).

fof(f70,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f702,plain,(
    ! [X0] :
      ( v2_tops_1(sK1,sK0)
      | ~ r1_tarski(X0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f229,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f229,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f228,f67])).

fof(f228,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f227,f68])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f76,f217])).

fof(f217,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0)
      | ~ r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f215,f104])).

fof(f215,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f211,f67])).

fof(f211,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f80,f68])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).

fof(f1898,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f1897,f116])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(resolution,[],[f99,f108])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f74,f72])).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1897,plain,(
    ! [X24] :
      ( ~ r1_tarski(k2_pre_topc(sK0,sK1),X24)
      | r1_tarski(sK1,X24) ) ),
    inference(subsumption_resolution,[],[f1893,f67])).

fof(f1893,plain,(
    ! [X24] :
      ( r1_tarski(sK1,X24)
      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X24)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f639,f68])).

fof(f639,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(X4,X6)
      | ~ r1_tarski(k2_pre_topc(X5,X4),X6)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f103,f273])).

fof(f273,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f270,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f270,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f78,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (14189)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.46  % (14180)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (14188)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (14183)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (14193)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (14185)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (14191)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (14182)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (14184)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (14179)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (14190)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (14194)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (14178)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (14192)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (14181)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (14186)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (14187)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (14195)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.09/0.62  % (14181)Refutation found. Thanks to Tanya!
% 2.09/0.62  % SZS status Theorem for theBenchmark
% 2.09/0.62  % SZS output start Proof for theBenchmark
% 2.09/0.62  fof(f1907,plain,(
% 2.09/0.62    $false),
% 2.09/0.62    inference(subsumption_resolution,[],[f1898,f921])).
% 2.09/0.62  fof(f921,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.09/0.62    inference(subsumption_resolution,[],[f920,f67])).
% 2.09/0.62  fof(f67,plain,(
% 2.09/0.62    l1_pre_topc(sK0)),
% 2.09/0.62    inference(cnf_transformation,[],[f62])).
% 2.09/0.62  fof(f62,plain,(
% 2.09/0.62    (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.09/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f61,f60])).
% 2.09/0.62  fof(f60,plain,(
% 2.09/0.62    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.09/0.62    introduced(choice_axiom,[])).
% 2.09/0.62  fof(f61,plain,(
% 2.09/0.62    ? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X1),sK0) & v3_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) & v3_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.09/0.62    introduced(choice_axiom,[])).
% 2.09/0.62  fof(f37,plain,(
% 2.09/0.62    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.09/0.62    inference(flattening,[],[f36])).
% 2.09/0.62  fof(f36,plain,(
% 2.09/0.62    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.09/0.62    inference(ennf_transformation,[],[f34])).
% 2.09/0.62  fof(f34,negated_conjecture,(
% 2.09/0.62    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.62    inference(negated_conjecture,[],[f33])).
% 2.09/0.62  fof(f33,conjecture,(
% 2.09/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 2.09/0.62  fof(f920,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f919,f68])).
% 2.09/0.62  fof(f68,plain,(
% 2.09/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.62    inference(cnf_transformation,[],[f62])).
% 2.09/0.62  fof(f919,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f918,f69])).
% 2.09/0.62  fof(f69,plain,(
% 2.09/0.62    v3_tops_1(sK1,sK0)),
% 2.09/0.62    inference(cnf_transformation,[],[f62])).
% 2.09/0.62  fof(f918,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v3_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(resolution,[],[f804,f83])).
% 2.09/0.62  fof(f83,plain,(
% 2.09/0.62    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f65])).
% 2.09/0.62  fof(f65,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(nnf_transformation,[],[f43])).
% 2.09/0.62  fof(f43,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(ennf_transformation,[],[f27])).
% 2.09/0.62  fof(f27,axiom,(
% 2.09/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_1)).
% 2.09/0.62  fof(f804,plain,(
% 2.09/0.62    ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.09/0.62    inference(subsumption_resolution,[],[f803,f68])).
% 2.09/0.62  fof(f803,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.62    inference(subsumption_resolution,[],[f792,f67])).
% 2.09/0.62  fof(f792,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.62    inference(resolution,[],[f703,f203])).
% 2.09/0.62  fof(f203,plain,(
% 2.09/0.62    ( ! [X6,X7] : (r1_tarski(k2_pre_topc(X6,X7),k2_tops_1(X6,k2_pre_topc(X6,X7))) | ~v2_tops_1(k2_pre_topc(X6,X7),X6) | ~l1_pre_topc(X6) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))) )),
% 2.09/0.62    inference(duplicate_literal_removal,[],[f199])).
% 2.09/0.62  fof(f199,plain,(
% 2.09/0.62    ( ! [X6,X7] : (~v2_tops_1(k2_pre_topc(X6,X7),X6) | r1_tarski(k2_pre_topc(X6,X7),k2_tops_1(X6,k2_pre_topc(X6,X7))) | ~l1_pre_topc(X6) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6)) )),
% 2.09/0.62    inference(resolution,[],[f79,f97])).
% 2.09/0.62  fof(f97,plain,(
% 2.09/0.62    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f50])).
% 2.09/0.62  fof(f50,plain,(
% 2.09/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(flattening,[],[f49])).
% 2.09/0.62  fof(f49,plain,(
% 2.09/0.62    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.09/0.62    inference(ennf_transformation,[],[f25])).
% 2.09/0.62  fof(f25,axiom,(
% 2.09/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.09/0.62  fof(f79,plain,(
% 2.09/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | r1_tarski(X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f63])).
% 2.09/0.62  fof(f63,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(nnf_transformation,[],[f41])).
% 2.09/0.62  fof(f41,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(ennf_transformation,[],[f32])).
% 2.09/0.62  fof(f32,axiom,(
% 2.09/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 2.09/0.62  fof(f703,plain,(
% 2.09/0.62    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~r1_tarski(sK1,X0)) )),
% 2.09/0.62    inference(subsumption_resolution,[],[f702,f238])).
% 2.09/0.62  fof(f238,plain,(
% 2.09/0.62    ~v2_tops_1(sK1,sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f237,f67])).
% 2.09/0.62  fof(f237,plain,(
% 2.09/0.62    ~v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f233,f68])).
% 2.09/0.62  fof(f233,plain,(
% 2.09/0.62    ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(resolution,[],[f81,f70])).
% 2.09/0.62  fof(f70,plain,(
% 2.09/0.62    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 2.09/0.62    inference(cnf_transformation,[],[f62])).
% 2.09/0.62  fof(f81,plain,(
% 2.09/0.62    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f64])).
% 2.09/0.62  fof(f64,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(nnf_transformation,[],[f42])).
% 2.09/0.62  fof(f42,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(ennf_transformation,[],[f26])).
% 2.09/0.62  fof(f26,axiom,(
% 2.09/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 2.09/0.62  fof(f702,plain,(
% 2.09/0.62    ( ! [X0] : (v2_tops_1(sK1,sK0) | ~r1_tarski(X0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~r1_tarski(sK1,X0)) )),
% 2.09/0.62    inference(resolution,[],[f229,f104])).
% 2.09/0.62  fof(f104,plain,(
% 2.09/0.62    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f57])).
% 2.09/0.62  fof(f57,plain,(
% 2.09/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.09/0.62    inference(flattening,[],[f56])).
% 2.09/0.62  fof(f56,plain,(
% 2.09/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.09/0.62    inference(ennf_transformation,[],[f5])).
% 2.09/0.62  fof(f5,axiom,(
% 2.09/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.09/0.62  fof(f229,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) | v2_tops_1(sK1,sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f228,f67])).
% 2.09/0.62  fof(f228,plain,(
% 2.09/0.62    ~l1_pre_topc(sK0) | v2_tops_1(sK1,sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 2.09/0.62    inference(subsumption_resolution,[],[f227,f68])).
% 2.09/0.62  fof(f227,plain,(
% 2.09/0.62    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tops_1(sK1,sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))),
% 2.09/0.62    inference(resolution,[],[f76,f217])).
% 2.09/0.62  fof(f217,plain,(
% 2.09/0.62    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~r1_tarski(sK1,X0)) )),
% 2.09/0.62    inference(resolution,[],[f215,f104])).
% 2.09/0.62  fof(f215,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 2.09/0.62    inference(subsumption_resolution,[],[f211,f67])).
% 2.09/0.62  fof(f211,plain,(
% 2.09/0.62    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.09/0.62    inference(resolution,[],[f80,f68])).
% 2.09/0.62  fof(f80,plain,(
% 2.09/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f63])).
% 2.09/0.62  fof(f76,plain,(
% 2.09/0.62    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f38])).
% 2.09/0.62  fof(f38,plain,(
% 2.09/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(ennf_transformation,[],[f31])).
% 2.09/0.62  fof(f31,axiom,(
% 2.09/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_tops_1(X0,k2_pre_topc(X0,X1)),k2_tops_1(X0,X1))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_1)).
% 2.09/0.62  fof(f1898,plain,(
% 2.09/0.62    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.09/0.62    inference(resolution,[],[f1897,f116])).
% 2.09/0.62  fof(f116,plain,(
% 2.09/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.09/0.62    inference(resolution,[],[f99,f108])).
% 2.09/0.62  fof(f108,plain,(
% 2.09/0.62    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.09/0.62    inference(forward_demodulation,[],[f74,f72])).
% 2.09/0.62  fof(f72,plain,(
% 2.09/0.62    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.09/0.62    inference(cnf_transformation,[],[f13])).
% 2.09/0.62  fof(f13,axiom,(
% 2.09/0.62    ! [X0] : k2_subset_1(X0) = X0),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.09/0.62  fof(f74,plain,(
% 2.09/0.62    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.09/0.62    inference(cnf_transformation,[],[f15])).
% 2.09/0.62  fof(f15,axiom,(
% 2.09/0.62    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.09/0.62  fof(f99,plain,(
% 2.09/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f66])).
% 2.09/0.62  fof(f66,plain,(
% 2.09/0.62    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.09/0.62    inference(nnf_transformation,[],[f23])).
% 2.09/0.62  fof(f23,axiom,(
% 2.09/0.62    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.09/0.62  fof(f1897,plain,(
% 2.09/0.62    ( ! [X24] : (~r1_tarski(k2_pre_topc(sK0,sK1),X24) | r1_tarski(sK1,X24)) )),
% 2.09/0.62    inference(subsumption_resolution,[],[f1893,f67])).
% 2.09/0.62  fof(f1893,plain,(
% 2.09/0.62    ( ! [X24] : (r1_tarski(sK1,X24) | ~r1_tarski(k2_pre_topc(sK0,sK1),X24) | ~l1_pre_topc(sK0)) )),
% 2.09/0.62    inference(resolution,[],[f639,f68])).
% 2.09/0.62  fof(f639,plain,(
% 2.09/0.62    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(X4,X6) | ~r1_tarski(k2_pre_topc(X5,X4),X6) | ~l1_pre_topc(X5)) )),
% 2.09/0.62    inference(superposition,[],[f103,f273])).
% 2.09/0.62  fof(f273,plain,(
% 2.09/0.62    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.09/0.62    inference(subsumption_resolution,[],[f270,f98])).
% 2.09/0.62  fof(f98,plain,(
% 2.09/0.62    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.62    inference(cnf_transformation,[],[f52])).
% 2.09/0.62  fof(f52,plain,(
% 2.09/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.09/0.62    inference(flattening,[],[f51])).
% 2.09/0.62  fof(f51,plain,(
% 2.09/0.62    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.09/0.62    inference(ennf_transformation,[],[f28])).
% 2.09/0.62  fof(f28,axiom,(
% 2.09/0.62    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.09/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.09/0.62  fof(f270,plain,(
% 2.09/0.62    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.09/0.62    inference(duplicate_literal_removal,[],[f267])).
% 2.09/0.63  fof(f267,plain,(
% 2.09/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.09/0.63    inference(superposition,[],[f78,f105])).
% 2.09/0.63  fof(f105,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.63    inference(cnf_transformation,[],[f59])).
% 2.09/0.63  fof(f59,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.63    inference(flattening,[],[f58])).
% 2.09/0.63  fof(f58,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.09/0.63    inference(ennf_transformation,[],[f17])).
% 2.09/0.63  fof(f17,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.09/0.63  fof(f78,plain,(
% 2.09/0.63    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f40])).
% 2.09/0.63  fof(f40,plain,(
% 2.09/0.63    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.63    inference(ennf_transformation,[],[f30])).
% 2.09/0.63  fof(f30,axiom,(
% 2.09/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.09/0.63  fof(f103,plain,(
% 2.09/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.09/0.63    inference(cnf_transformation,[],[f55])).
% 2.09/0.63  fof(f55,plain,(
% 2.09/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.09/0.63    inference(ennf_transformation,[],[f3])).
% 2.09/0.63  fof(f3,axiom,(
% 2.09/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.09/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.09/0.63  % SZS output end Proof for theBenchmark
% 2.09/0.63  % (14181)------------------------------
% 2.09/0.63  % (14181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.63  % (14181)Termination reason: Refutation
% 2.09/0.63  
% 2.09/0.63  % (14181)Memory used [KB]: 3070
% 2.09/0.63  % (14181)Time elapsed: 0.211 s
% 2.09/0.63  % (14181)------------------------------
% 2.09/0.63  % (14181)------------------------------
% 2.09/0.63  % (14177)Success in time 0.27 s
%------------------------------------------------------------------------------
