%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:11 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 644 expanded)
%              Number of leaves         :   21 ( 212 expanded)
%              Depth                    :   19
%              Number of atoms          :  274 (2297 expanded)
%              Number of equality atoms :   78 ( 192 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5251,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5250,f283])).

fof(f283,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f281,f190])).

fof(f190,plain,(
    ! [X3] : k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X3) ),
    inference(resolution,[],[f135,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f135,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f132,f49])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f132,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f61,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f281,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(superposition,[],[f52,f126])).

fof(f126,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f71,f50])).

fof(f52,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f5250,plain,(
    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(forward_demodulation,[],[f5240,f1875])).

fof(f1875,plain,(
    ! [X12] : k1_tops_1(sK0,k4_xboole_0(sK1,X12)) = k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X12)) ),
    inference(forward_demodulation,[],[f1874,f1213])).

fof(f1213,plain,(
    ! [X30] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(sK1,X30)) ),
    inference(forward_demodulation,[],[f1212,f445])).

fof(f445,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(forward_demodulation,[],[f444,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f444,plain,(
    ! [X0] : k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)) = k4_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f443,f250])).

fof(f250,plain,(
    ! [X10,X9] : k4_xboole_0(k4_xboole_0(sK1,X9),X10) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X9),X10) ),
    inference(forward_demodulation,[],[f235,f126])).

fof(f235,plain,(
    ! [X10,X9] : k4_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X9),X10) = k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X9),X10) ),
    inference(resolution,[],[f105,f71])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f70,f50])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f443,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)) ),
    inference(forward_demodulation,[],[f442,f423])).

fof(f423,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f101,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f101,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f68,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f442,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f441,f126])).

fof(f441,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) ),
    inference(forward_demodulation,[],[f440,f58])).

fof(f440,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f431,f286])).

fof(f286,plain,(
    ! [X2,X3] : k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2) ),
    inference(resolution,[],[f79,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f79,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f67,f74])).

fof(f74,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f431,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f147,f105])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | k7_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,X3,X2) ) ),
    inference(forward_demodulation,[],[f144,f99])).

fof(f99,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f98,f54])).

fof(f98,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f59,f53])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f144,plain,(
    ! [X2,X3] :
      ( k7_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,X3,k3_subset_1(X2,k1_xboole_0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f60,f53])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1212,plain,(
    ! [X30] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X30))) ),
    inference(forward_demodulation,[],[f1198,f58])).

fof(f1198,plain,(
    ! [X30] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X30),sK1)) ),
    inference(resolution,[],[f295,f153])).

fof(f153,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(X0,sK1)) ) ),
    inference(forward_demodulation,[],[f152,f129])).

fof(f129,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(resolution,[],[f72,f50])).

fof(f152,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f151,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f151,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f49])).

fof(f148,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tops_1)).

fof(f295,plain,(
    ! [X6,X7] : m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(X6)) ),
    inference(forward_demodulation,[],[f288,f287])).

fof(f287,plain,(
    ! [X4,X5] : k4_xboole_0(X4,X5) = k7_subset_1(X4,X4,X5) ),
    inference(resolution,[],[f79,f71])).

fof(f288,plain,(
    ! [X6,X7] : m1_subset_1(k7_subset_1(X6,X6,X7),k1_zfmisc_1(X6)) ),
    inference(resolution,[],[f79,f70])).

fof(f1874,plain,(
    ! [X12] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X12)) ),
    inference(forward_demodulation,[],[f1873,f786])).

fof(f786,plain,(
    ! [X20] : k4_xboole_0(k1_tops_1(sK0,sK1),X20) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20)) ),
    inference(forward_demodulation,[],[f785,f54])).

fof(f785,plain,(
    ! [X20] : k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20)) = k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) ),
    inference(forward_demodulation,[],[f784,f765])).

fof(f765,plain,(
    ! [X17,X16] : k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X16),X17) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X16),X17) ),
    inference(resolution,[],[f203,f71])).

fof(f203,plain,(
    ! [X4] : m1_subset_1(k4_xboole_0(k1_tops_1(sK0,sK1),X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f191,f190])).

fof(f191,plain,(
    ! [X4] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f135,f70])).

fof(f784,plain,(
    ! [X20] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20)) ),
    inference(forward_demodulation,[],[f783,f58])).

fof(f783,plain,(
    ! [X20] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k3_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X20),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f767,f286])).

fof(f767,plain,(
    ! [X20] : k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),u1_struct_0(sK0)) ),
    inference(resolution,[],[f203,f147])).

fof(f1873,plain,(
    ! [X12] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X12))) ),
    inference(forward_demodulation,[],[f1872,f423])).

fof(f1872,plain,(
    ! [X12] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X12))) ),
    inference(forward_demodulation,[],[f1871,f58])).

fof(f1871,plain,(
    ! [X12] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X12),k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1800,f189])).

fof(f189,plain,(
    ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,k1_tops_1(sK0,sK1)) = k3_xboole_0(X2,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f135,f72])).

fof(f1800,plain,(
    ! [X12] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X12),k1_tops_1(sK0,sK1))) ),
    inference(resolution,[],[f196,f295])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))) ) ),
    inference(forward_demodulation,[],[f195,f140])).

fof(f140,plain,(
    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f137,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f50])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f195,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f194,f48])).

fof(f194,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f49])).

fof(f184,plain,(
    ! [X0] :
      ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f135,f56])).

fof(f5240,plain,(
    r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f781,f741])).

fof(f741,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k4_xboole_0(X3,sK2))
      | r1_tarski(X2,k4_xboole_0(X3,k1_tops_1(sK0,sK2))) ) ),
    inference(resolution,[],[f171,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f171,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f125,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f125,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f55,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f781,plain,(
    ! [X9] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X9)),k4_xboole_0(k1_tops_1(sK0,sK1),X9)) ),
    inference(subsumption_resolution,[],[f760,f49])).

fof(f760,plain,(
    ! [X9] :
      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X9)),k4_xboole_0(k1_tops_1(sK0,sK1),X9))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f203,f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:45:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (32376)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (32389)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (32372)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (32388)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (32371)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (32380)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (32370)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (32382)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (32385)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (32378)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (32387)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (32374)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (32391)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (32383)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (32377)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (32384)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (32373)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (32379)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.54  % (32390)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (32375)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (32381)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (32392)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.55  % (32394)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (32393)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (32395)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (32386)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.72/0.71  % (32380)Refutation found. Thanks to Tanya!
% 2.72/0.71  % SZS status Theorem for theBenchmark
% 2.72/0.71  % SZS output start Proof for theBenchmark
% 2.72/0.71  fof(f5251,plain,(
% 2.72/0.71    $false),
% 2.72/0.71    inference(subsumption_resolution,[],[f5250,f283])).
% 2.72/0.71  fof(f283,plain,(
% 2.72/0.71    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.72/0.71    inference(forward_demodulation,[],[f281,f190])).
% 2.72/0.71  fof(f190,plain,(
% 2.72/0.71    ( ! [X3] : (k4_xboole_0(k1_tops_1(sK0,sK1),X3) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X3)) )),
% 2.72/0.71    inference(resolution,[],[f135,f71])).
% 2.72/0.71  fof(f71,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f37])).
% 2.72/0.71  fof(f37,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f10])).
% 2.72/0.71  fof(f10,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.72/0.71  fof(f135,plain,(
% 2.72/0.71    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.72/0.71    inference(subsumption_resolution,[],[f132,f49])).
% 2.72/0.71  fof(f49,plain,(
% 2.72/0.71    l1_pre_topc(sK0)),
% 2.72/0.71    inference(cnf_transformation,[],[f44])).
% 2.72/0.71  fof(f44,plain,(
% 2.72/0.71    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.72/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f43,f42,f41])).
% 2.72/0.71  fof(f41,plain,(
% 2.72/0.71    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.72/0.71    introduced(choice_axiom,[])).
% 2.72/0.71  fof(f42,plain,(
% 2.72/0.71    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.72/0.71    introduced(choice_axiom,[])).
% 2.72/0.71  fof(f43,plain,(
% 2.72/0.71    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.72/0.71    introduced(choice_axiom,[])).
% 2.72/0.71  fof(f25,plain,(
% 2.72/0.71    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.72/0.71    inference(flattening,[],[f24])).
% 2.72/0.71  fof(f24,plain,(
% 2.72/0.71    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f21])).
% 2.72/0.71  fof(f21,negated_conjecture,(
% 2.72/0.71    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.72/0.71    inference(negated_conjecture,[],[f20])).
% 2.72/0.71  fof(f20,conjecture,(
% 2.72/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 2.72/0.71  fof(f132,plain,(
% 2.72/0.71    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.72/0.71    inference(resolution,[],[f61,f50])).
% 2.72/0.71  fof(f50,plain,(
% 2.72/0.71    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.72/0.71    inference(cnf_transformation,[],[f44])).
% 2.72/0.71  fof(f61,plain,(
% 2.72/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f32])).
% 2.72/0.71  fof(f32,plain,(
% 2.72/0.71    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.72/0.71    inference(flattening,[],[f31])).
% 2.72/0.71  fof(f31,plain,(
% 2.72/0.71    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f16])).
% 2.72/0.71  fof(f16,axiom,(
% 2.72/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 2.72/0.71  fof(f281,plain,(
% 2.72/0.71    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.72/0.71    inference(superposition,[],[f52,f126])).
% 2.72/0.71  fof(f126,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.72/0.71    inference(resolution,[],[f71,f50])).
% 2.72/0.71  fof(f52,plain,(
% 2.72/0.71    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.72/0.71    inference(cnf_transformation,[],[f44])).
% 2.72/0.71  fof(f5250,plain,(
% 2.72/0.71    r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.72/0.71    inference(forward_demodulation,[],[f5240,f1875])).
% 2.72/0.71  fof(f1875,plain,(
% 2.72/0.71    ( ! [X12] : (k1_tops_1(sK0,k4_xboole_0(sK1,X12)) = k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X12))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1874,f1213])).
% 2.72/0.71  fof(f1213,plain,(
% 2.72/0.71    ( ! [X30] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(sK1,X30))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1212,f445])).
% 2.72/0.71  fof(f445,plain,(
% 2.72/0.71    ( ! [X0] : (k4_xboole_0(sK1,X0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f444,f54])).
% 2.72/0.71  fof(f54,plain,(
% 2.72/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.72/0.71    inference(cnf_transformation,[],[f6])).
% 2.72/0.71  fof(f6,axiom,(
% 2.72/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.72/0.71  fof(f444,plain,(
% 2.72/0.71    ( ! [X0] : (k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0)) = k4_xboole_0(k4_xboole_0(sK1,X0),k1_xboole_0)) )),
% 2.72/0.71    inference(forward_demodulation,[],[f443,f250])).
% 2.72/0.71  fof(f250,plain,(
% 2.72/0.71    ( ! [X10,X9] : (k4_xboole_0(k4_xboole_0(sK1,X9),X10) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X9),X10)) )),
% 2.72/0.71    inference(forward_demodulation,[],[f235,f126])).
% 2.72/0.71  fof(f235,plain,(
% 2.72/0.71    ( ! [X10,X9] : (k4_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X9),X10) = k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X9),X10)) )),
% 2.72/0.71    inference(resolution,[],[f105,f71])).
% 2.72/0.71  fof(f105,plain,(
% 2.72/0.71    ( ! [X0] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.72/0.71    inference(resolution,[],[f70,f50])).
% 2.72/0.71  fof(f70,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 2.72/0.71    inference(cnf_transformation,[],[f36])).
% 2.72/0.71  fof(f36,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f9])).
% 2.72/0.71  fof(f9,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.72/0.71  fof(f443,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f442,f423])).
% 2.72/0.71  fof(f423,plain,(
% 2.72/0.71    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 2.72/0.71    inference(superposition,[],[f101,f68])).
% 2.72/0.71  fof(f68,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f7])).
% 2.72/0.71  fof(f7,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.72/0.71  fof(f101,plain,(
% 2.72/0.71    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X3,X4)) = k4_xboole_0(k3_xboole_0(X3,X2),X4)) )),
% 2.72/0.71    inference(superposition,[],[f68,f58])).
% 2.72/0.71  fof(f58,plain,(
% 2.72/0.71    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f1])).
% 2.72/0.71  fof(f1,axiom,(
% 2.72/0.71    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.72/0.71  fof(f442,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X0),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(sK1,X0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f441,f126])).
% 2.72/0.71  fof(f441,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f440,f58])).
% 2.72/0.71  fof(f440,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k3_xboole_0(k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f431,f286])).
% 2.72/0.71  fof(f286,plain,(
% 2.72/0.71    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = k9_subset_1(X2,X3,X2)) )),
% 2.72/0.71    inference(resolution,[],[f79,f72])).
% 2.72/0.71  fof(f72,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f38])).
% 2.72/0.71  fof(f38,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f11])).
% 2.72/0.71  fof(f11,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.72/0.71  fof(f79,plain,(
% 2.72/0.71    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.72/0.71    inference(resolution,[],[f67,f74])).
% 2.72/0.71  fof(f74,plain,(
% 2.72/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.72/0.71    inference(equality_resolution,[],[f64])).
% 2.72/0.71  fof(f64,plain,(
% 2.72/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.72/0.71    inference(cnf_transformation,[],[f46])).
% 2.72/0.71  fof(f46,plain,(
% 2.72/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.72/0.71    inference(flattening,[],[f45])).
% 2.72/0.71  fof(f45,plain,(
% 2.72/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.72/0.71    inference(nnf_transformation,[],[f3])).
% 2.72/0.71  fof(f3,axiom,(
% 2.72/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.72/0.71  fof(f67,plain,(
% 2.72/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.72/0.71    inference(cnf_transformation,[],[f47])).
% 2.72/0.71  fof(f47,plain,(
% 2.72/0.71    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.72/0.71    inference(nnf_transformation,[],[f14])).
% 2.72/0.71  fof(f14,axiom,(
% 2.72/0.71    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.72/0.71  fof(f431,plain,(
% 2.72/0.71    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0),u1_struct_0(sK0))) )),
% 2.72/0.71    inference(resolution,[],[f147,f105])).
% 2.72/0.71  fof(f147,plain,(
% 2.72/0.71    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | k7_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,X3,X2)) )),
% 2.72/0.71    inference(forward_demodulation,[],[f144,f99])).
% 2.72/0.71  fof(f99,plain,(
% 2.72/0.71    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.72/0.71    inference(forward_demodulation,[],[f98,f54])).
% 2.72/0.71  fof(f98,plain,(
% 2.72/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.72/0.71    inference(resolution,[],[f59,f53])).
% 2.72/0.71  fof(f53,plain,(
% 2.72/0.71    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.72/0.71    inference(cnf_transformation,[],[f13])).
% 2.72/0.71  fof(f13,axiom,(
% 2.72/0.71    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.72/0.71  fof(f59,plain,(
% 2.72/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f29])).
% 2.72/0.71  fof(f29,plain,(
% 2.72/0.71    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f8])).
% 2.72/0.71  fof(f8,axiom,(
% 2.72/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.72/0.71  fof(f144,plain,(
% 2.72/0.71    ( ! [X2,X3] : (k7_subset_1(X2,X3,k1_xboole_0) = k9_subset_1(X2,X3,k3_subset_1(X2,k1_xboole_0)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.72/0.71    inference(resolution,[],[f60,f53])).
% 2.72/0.71  fof(f60,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.72/0.71    inference(cnf_transformation,[],[f30])).
% 2.72/0.71  fof(f30,plain,(
% 2.72/0.71    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f12])).
% 2.72/0.71  fof(f12,axiom,(
% 2.72/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.72/0.71  fof(f1212,plain,(
% 2.72/0.71    ( ! [X30] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),X30)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1198,f58])).
% 2.72/0.71  fof(f1198,plain,(
% 2.72/0.71    ( ! [X30] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X30)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X30),sK1))) )),
% 2.72/0.71    inference(resolution,[],[f295,f153])).
% 2.72/0.71  fof(f153,plain,(
% 2.72/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(X0,sK1))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f152,f129])).
% 2.72/0.71  fof(f129,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) )),
% 2.72/0.71    inference(resolution,[],[f72,f50])).
% 2.72/0.71  fof(f152,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.72/0.71    inference(subsumption_resolution,[],[f151,f48])).
% 2.72/0.71  fof(f48,plain,(
% 2.72/0.71    v2_pre_topc(sK0)),
% 2.72/0.71    inference(cnf_transformation,[],[f44])).
% 2.72/0.71  fof(f151,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 2.72/0.71    inference(subsumption_resolution,[],[f148,f49])).
% 2.72/0.71  fof(f148,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 2.72/0.71    inference(resolution,[],[f56,f50])).
% 2.72/0.71  fof(f56,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f28])).
% 2.72/0.71  fof(f28,plain,(
% 2.72/0.71    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.72/0.71    inference(flattening,[],[f27])).
% 2.72/0.71  fof(f27,plain,(
% 2.72/0.71    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f19])).
% 2.72/0.71  fof(f19,axiom,(
% 2.72/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_tops_1)).
% 2.72/0.71  fof(f295,plain,(
% 2.72/0.71    ( ! [X6,X7] : (m1_subset_1(k4_xboole_0(X6,X7),k1_zfmisc_1(X6))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f288,f287])).
% 2.72/0.71  fof(f287,plain,(
% 2.72/0.71    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k7_subset_1(X4,X4,X5)) )),
% 2.72/0.71    inference(resolution,[],[f79,f71])).
% 2.72/0.71  fof(f288,plain,(
% 2.72/0.71    ( ! [X6,X7] : (m1_subset_1(k7_subset_1(X6,X6,X7),k1_zfmisc_1(X6))) )),
% 2.72/0.71    inference(resolution,[],[f79,f70])).
% 2.72/0.71  fof(f1874,plain,(
% 2.72/0.71    ( ! [X12] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X12))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1873,f786])).
% 2.72/0.71  fof(f786,plain,(
% 2.72/0.71    ( ! [X20] : (k4_xboole_0(k1_tops_1(sK0,sK1),X20) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f785,f54])).
% 2.72/0.71  fof(f785,plain,(
% 2.72/0.71    ( ! [X20] : (k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20)) = k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0)) )),
% 2.72/0.71    inference(forward_demodulation,[],[f784,f765])).
% 2.72/0.71  fof(f765,plain,(
% 2.72/0.71    ( ! [X17,X16] : (k4_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X16),X17) = k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X16),X17)) )),
% 2.72/0.71    inference(resolution,[],[f203,f71])).
% 2.72/0.71  fof(f203,plain,(
% 2.72/0.71    ( ! [X4] : (m1_subset_1(k4_xboole_0(k1_tops_1(sK0,sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f191,f190])).
% 2.72/0.71  fof(f191,plain,(
% 2.72/0.71    ( ! [X4] : (m1_subset_1(k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X4),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.72/0.71    inference(resolution,[],[f135,f70])).
% 2.72/0.71  fof(f784,plain,(
% 2.72/0.71    ( ! [X20] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f783,f58])).
% 2.72/0.71  fof(f783,plain,(
% 2.72/0.71    ( ! [X20] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k3_xboole_0(k4_xboole_0(k1_tops_1(sK0,sK1),X20),u1_struct_0(sK0))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f767,f286])).
% 2.72/0.71  fof(f767,plain,(
% 2.72/0.71    ( ! [X20] : (k7_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X20),u1_struct_0(sK0))) )),
% 2.72/0.71    inference(resolution,[],[f203,f147])).
% 2.72/0.71  fof(f1873,plain,(
% 2.72/0.71    ( ! [X12] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(k1_tops_1(sK0,sK1),X12)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1872,f423])).
% 2.72/0.71  fof(f1872,plain,(
% 2.72/0.71    ( ! [X12] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k1_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),X12)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1871,f58])).
% 2.72/0.71  fof(f1871,plain,(
% 2.72/0.71    ( ! [X12] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),X12),k1_tops_1(sK0,sK1)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f1800,f189])).
% 2.72/0.71  fof(f189,plain,(
% 2.72/0.71    ( ! [X2] : (k9_subset_1(u1_struct_0(sK0),X2,k1_tops_1(sK0,sK1)) = k3_xboole_0(X2,k1_tops_1(sK0,sK1))) )),
% 2.72/0.71    inference(resolution,[],[f135,f72])).
% 2.72/0.71  fof(f1800,plain,(
% 2.72/0.71    ( ! [X12] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),X12)),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),X12),k1_tops_1(sK0,sK1)))) )),
% 2.72/0.71    inference(resolution,[],[f196,f295])).
% 2.72/0.71  fof(f196,plain,(
% 2.72/0.71    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1)))) )),
% 2.72/0.71    inference(forward_demodulation,[],[f195,f140])).
% 2.72/0.71  fof(f140,plain,(
% 2.72/0.71    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 2.72/0.71    inference(subsumption_resolution,[],[f137,f49])).
% 2.72/0.71  fof(f137,plain,(
% 2.72/0.71    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.72/0.71    inference(resolution,[],[f62,f50])).
% 2.72/0.71  fof(f62,plain,(
% 2.72/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f34])).
% 2.72/0.71  fof(f34,plain,(
% 2.72/0.71    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.72/0.71    inference(flattening,[],[f33])).
% 2.72/0.71  fof(f33,plain,(
% 2.72/0.71    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.72/0.71    inference(ennf_transformation,[],[f17])).
% 2.72/0.71  fof(f17,axiom,(
% 2.72/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 2.72/0.71  fof(f195,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.72/0.71    inference(subsumption_resolution,[],[f194,f48])).
% 2.72/0.71  fof(f194,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 2.72/0.71    inference(subsumption_resolution,[],[f184,f49])).
% 2.72/0.71  fof(f184,plain,(
% 2.72/0.71    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X0),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 2.72/0.71    inference(resolution,[],[f135,f56])).
% 2.72/0.71  fof(f5240,plain,(
% 2.72/0.71    r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.72/0.71    inference(resolution,[],[f781,f741])).
% 2.72/0.71  fof(f741,plain,(
% 2.72/0.71    ( ! [X2,X3] : (~r1_tarski(X2,k4_xboole_0(X3,sK2)) | r1_tarski(X2,k4_xboole_0(X3,k1_tops_1(sK0,sK2)))) )),
% 2.72/0.71    inference(resolution,[],[f171,f73])).
% 2.72/0.71  fof(f73,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f40])).
% 2.72/0.71  fof(f40,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.72/0.71    inference(flattening,[],[f39])).
% 2.72/0.71  fof(f39,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.72/0.71    inference(ennf_transformation,[],[f4])).
% 2.72/0.71  fof(f4,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.72/0.71  fof(f171,plain,(
% 2.72/0.71    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK2),k4_xboole_0(X0,k1_tops_1(sK0,sK2)))) )),
% 2.72/0.71    inference(resolution,[],[f125,f69])).
% 2.72/0.71  fof(f69,plain,(
% 2.72/0.71    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 2.72/0.71    inference(cnf_transformation,[],[f35])).
% 2.72/0.71  fof(f35,plain,(
% 2.72/0.71    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 2.72/0.71    inference(ennf_transformation,[],[f5])).
% 2.72/0.71  fof(f5,axiom,(
% 2.72/0.71    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).
% 2.72/0.71  fof(f125,plain,(
% 2.72/0.71    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.72/0.71    inference(subsumption_resolution,[],[f122,f49])).
% 2.72/0.71  fof(f122,plain,(
% 2.72/0.71    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 2.72/0.71    inference(resolution,[],[f55,f51])).
% 2.72/0.71  fof(f51,plain,(
% 2.72/0.71    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.72/0.71    inference(cnf_transformation,[],[f44])).
% 2.72/0.71  fof(f55,plain,(
% 2.72/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.72/0.71    inference(cnf_transformation,[],[f26])).
% 2.72/0.71  fof(f26,plain,(
% 2.72/0.71    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/0.71    inference(ennf_transformation,[],[f18])).
% 2.72/0.71  fof(f18,axiom,(
% 2.72/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.72/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.72/0.71  fof(f781,plain,(
% 2.72/0.71    ( ! [X9] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X9)),k4_xboole_0(k1_tops_1(sK0,sK1),X9))) )),
% 2.72/0.71    inference(subsumption_resolution,[],[f760,f49])).
% 2.72/0.71  fof(f760,plain,(
% 2.72/0.71    ( ! [X9] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(k1_tops_1(sK0,sK1),X9)),k4_xboole_0(k1_tops_1(sK0,sK1),X9)) | ~l1_pre_topc(sK0)) )),
% 2.72/0.71    inference(resolution,[],[f203,f55])).
% 2.72/0.71  % SZS output end Proof for theBenchmark
% 2.72/0.71  % (32380)------------------------------
% 2.72/0.71  % (32380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.71  % (32380)Termination reason: Refutation
% 2.72/0.71  
% 2.72/0.71  % (32380)Memory used [KB]: 13432
% 2.72/0.71  % (32380)Time elapsed: 0.301 s
% 2.72/0.71  % (32380)------------------------------
% 2.72/0.71  % (32380)------------------------------
% 2.72/0.71  % (32369)Success in time 0.357 s
%------------------------------------------------------------------------------
