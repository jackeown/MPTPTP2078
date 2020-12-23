%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1232+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:31 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 374 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   19
%              Number of atoms          :  264 (1795 expanded)
%              Number of equality atoms :   38 ( 357 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3755,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3754,f175])).

fof(f175,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f164,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f164,plain,(
    ! [X6] : m1_subset_1(k3_xboole_0(X6,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK1) = k3_xboole_0(X5,sK1) ),
    inference(resolution,[],[f37,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)))
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
                & v3_pre_topc(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)))
              & v3_pre_topc(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,k2_pre_topc(sK0,X2)))
            & v3_pre_topc(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)))
          & v3_pre_topc(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X2)))
        & v3_pre_topc(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)))
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X1,X0)
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f75,plain,(
    ! [X6] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X6,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f37,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f3754,plain,(
    ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3753,f175])).

fof(f3753,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3750,f1138])).

fof(f1138,plain,(
    r1_tarski(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1137,f44])).

fof(f1137,plain,(
    r1_tarski(k3_xboole_0(k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1136,f318])).

fof(f318,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),sK1,X4) = k3_xboole_0(X4,sK1) ),
    inference(forward_demodulation,[],[f73,f74])).

fof(f73,plain,(
    ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X4) ),
    inference(resolution,[],[f37,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f1136,plain,(
    r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f1135,f37])).

fof(f1135,plain,
    ( r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1058,f39])).

fof(f39,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f1058,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(X3,sK2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f102,f94])).

fof(f94,plain,(
    ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,sK2) = k3_xboole_0(X5,sK2) ),
    inference(resolution,[],[f38,f52])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X3] :
      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,(
    ! [X3] :
      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f90,plain,(
    ! [X3] :
      ( r1_tarski(k9_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK2)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_tops_1)).

fof(f3750,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f3336,f587])).

fof(f587,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X2))
      | ~ r1_tarski(X3,k2_pre_topc(sK0,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f586,f58])).

fof(f58,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f36,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f586,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X2))
      | ~ r1_tarski(X3,k2_pre_topc(sK0,X2))
      | ~ m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f579,f36])).

fof(f579,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X2))
      | ~ r1_tarski(X3,k2_pre_topc(sK0,X2))
      | ~ m1_subset_1(k2_pre_topc(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f60,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f60,plain,(
    ! [X4,X5] :
      ( r1_tarski(k2_pre_topc(sK0,X4),k2_pre_topc(sK0,X5))
      | ~ r1_tarski(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f3336,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f3333,f331])).

fof(f331,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f319,f44])).

fof(f319,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK2),sK1)) ),
    inference(backward_demodulation,[],[f220,f318])).

fof(f220,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f40,f94])).

fof(f40,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3333,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f3312,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f3312,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f3311,f44])).

fof(f3311,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)))) ),
    inference(forward_demodulation,[],[f3310,f44])).

fof(f3310,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK2),sK1))) ),
    inference(subsumption_resolution,[],[f3278,f243])).

fof(f243,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f232,f44])).

fof(f232,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(X4,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f226,f38])).

fof(f226,plain,(
    ! [X4] :
      ( m1_subset_1(k3_xboole_0(X4,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f51,f94])).

fof(f3278,plain,
    ( r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)),k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK2),sK1)))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f179,f110])).

fof(f110,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(k2_pre_topc(sK0,sK2),X0)) ),
    inference(resolution,[],[f96,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_xboole_1)).

fof(f96,plain,(
    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f86,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f179,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k3_xboole_0(X4,sK1))
      | r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,k3_xboole_0(X4,sK1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f167,f36])).

fof(f167,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,k3_xboole_0(X4,sK1)))
      | ~ r1_tarski(X3,k3_xboole_0(X4,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f164,f42])).

%------------------------------------------------------------------------------
