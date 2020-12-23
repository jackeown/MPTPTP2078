%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 146 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   18
%              Number of atoms          :  192 ( 534 expanded)
%              Number of equality atoms :   37 (  45 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(subsumption_resolution,[],[f337,f47])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f337,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f332,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f332,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f319,f125])).

fof(f125,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f124,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    & v5_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
            & v5_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
          & v5_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1)))
        & v5_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
      & v5_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1)))
          & v5_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v5_tops_1(X1,X0)
             => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).

fof(f124,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f123,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f32,plain,(
    v5_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f120,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ v5_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).

fof(f33,plain,(
    ~ r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f319,plain,(
    ! [X6] :
      ( r1_tarski(k2_tops_1(sK0,sK1),X6)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f67,f252])).

fof(f252,plain,(
    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f228,f31])).

fof(f228,plain,
    ( k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f226,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X2,X1) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X2,X1) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f45,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f226,plain,(
    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f225,f30])).

fof(f225,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f207,f31])).

fof(f207,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f34,f135])).

fof(f135,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f134,f32])).

fof(f134,plain,
    ( ~ v5_tops_1(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f132,f30])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v5_tops_1(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f126,f31])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f122,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f38,f35])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f62,f45])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:50:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (26122)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (26130)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.48  % (26117)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (26131)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.49  % (26123)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (26115)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (26113)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (26115)Refutation not found, incomplete strategy% (26115)------------------------------
% 0.21/0.49  % (26115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26115)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (26115)Memory used [KB]: 10618
% 0.21/0.49  % (26115)Time elapsed: 0.096 s
% 0.21/0.49  % (26115)------------------------------
% 0.21/0.49  % (26115)------------------------------
% 0.21/0.50  % (26109)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (26118)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (26134)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.50  % (26113)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f338,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f337,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    ~r1_tarski(sK1,sK1)),
% 0.21/0.50    inference(resolution,[],[f332,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.50    inference(resolution,[],[f319,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f124,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f24,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X1] : (~r1_tarski(k2_tops_1(sK0,X1),k2_pre_topc(sK0,k1_tops_1(sK0,X1))) & v5_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) & v5_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((~r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))) & v5_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => r1_tarski(k2_tops_1(X0,X1),k2_pre_topc(X0,k1_tops_1(X0,X1))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tops_1)).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    v5_tops_1(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~v5_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(superposition,[],[f33,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tops_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ~r1_tarski(k2_tops_1(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    ( ! [X6] : (r1_tarski(k2_tops_1(sK0,sK1),X6) | ~m1_subset_1(sK1,k1_zfmisc_1(X6))) )),
% 0.21/0.50    inference(superposition,[],[f67,f252])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f228,f31])).
% 0.21/0.50  fof(f228,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k3_xboole_0(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(superposition,[],[f226,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X2,X1) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X2,X1) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f45,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.50  fof(f226,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f225,f30])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f207,f31])).
% 0.21/0.50  fof(f207,plain,(
% 0.21/0.50    k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(superposition,[],[f34,f135])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f32])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~v5_tops_1(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f132,f30])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~v5_tops_1(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f126,f31])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(superposition,[],[f38,f35])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k2_pre_topc)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(superposition,[],[f62,f45])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(resolution,[],[f44,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (26113)------------------------------
% 0.21/0.50  % (26113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26113)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (26113)Memory used [KB]: 6268
% 0.21/0.50  % (26113)Time elapsed: 0.091 s
% 0.21/0.50  % (26113)------------------------------
% 0.21/0.50  % (26113)------------------------------
% 0.21/0.50  % (26126)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (26108)Success in time 0.154 s
%------------------------------------------------------------------------------
