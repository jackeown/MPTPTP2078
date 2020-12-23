%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:53 EST 2020

% Result     : Theorem 2.49s
% Output     : Refutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 369 expanded)
%              Number of leaves         :   13 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  179 (1541 expanded)
%              Number of equality atoms :   41 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2042,plain,(
    $false ),
    inference(resolution,[],[f2040,f1698])).

fof(f1698,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f33,f1659])).

fof(f1659,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f1641,f524])).

fof(f524,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f511,f115])).

fof(f115,plain,(
    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(resolution,[],[f108,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) ) ),
    inference(resolution,[],[f40,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f511,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(resolution,[],[f310,f29])).

fof(f310,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) ) ),
    inference(resolution,[],[f185,f30])).

fof(f185,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f120,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
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
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f1641,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f1622,f30])).

fof(f1622,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f722,f29])).

fof(f722,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = k2_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ) ),
    inference(resolution,[],[f295,f28])).

fof(f295,plain,(
    ! [X17,X16] :
      ( ~ l1_pre_topc(sK0)
      | k2_xboole_0(k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17))
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f191,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f191,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(k2_pre_topc(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f112,f28])).

fof(f112,plain,(
    ! [X6,X8,X7] :
      ( ~ l1_pre_topc(X7)
      | k2_xboole_0(k2_pre_topc(X7,X8),X6) = k4_subset_1(u1_struct_0(X7),k2_pre_topc(X7,X8),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) ) ),
    inference(resolution,[],[f40,f36])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f2040,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f2039,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2039,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f2038,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2038,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f184,f2037])).

fof(f2037,plain,(
    ! [X0] : k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f2018,f1399])).

fof(f1399,plain,(
    ! [X1] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X1))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f1381,f123])).

fof(f123,plain,(
    ! [X0] : k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f109,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f78,f29])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f37,f74])).

fof(f74,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f38,f29])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f109,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(sK2,X1) = k4_subset_1(u1_struct_0(sK0),sK2,X1) ) ),
    inference(resolution,[],[f40,f30])).

fof(f1381,plain,(
    ! [X1] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X1))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X1))) ),
    inference(resolution,[],[f311,f30])).

fof(f311,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k2_pre_topc(sK0,k4_xboole_0(sK1,X3))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,k4_xboole_0(sK1,X3))) ) ),
    inference(resolution,[],[f185,f80])).

fof(f2018,plain,(
    ! [X0] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) ),
    inference(resolution,[],[f1623,f80])).

fof(f1623,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X1)) ) ),
    inference(resolution,[],[f722,f30])).

fof(f184,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f183,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f183,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f77,f175])).

fof(f175,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f152,f29])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f92,f28])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2) ) ),
    inference(resolution,[],[f36,f38])).

fof(f77,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f31,f74])).

fof(f31,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:11:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (26844)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.48  % (26852)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.48  % (26845)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (26837)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.49  % (26838)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.49  % (26842)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.50  % (26834)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (26855)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.50  % (26847)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (26853)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (26835)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (26836)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (26839)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (26836)Refutation not found, incomplete strategy% (26836)------------------------------
% 0.22/0.51  % (26836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26836)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (26836)Memory used [KB]: 10490
% 0.22/0.51  % (26836)Time elapsed: 0.093 s
% 0.22/0.51  % (26836)------------------------------
% 0.22/0.51  % (26836)------------------------------
% 0.22/0.51  % (26841)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (26843)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (26833)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.52  % (26851)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (26854)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (26846)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (26850)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.35/0.53  % (26849)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.35/0.53  % (26840)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.35/0.54  % (26856)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.35/0.54  % (26848)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.35/0.54  % (26856)Refutation not found, incomplete strategy% (26856)------------------------------
% 1.35/0.54  % (26856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (26856)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (26856)Memory used [KB]: 10618
% 1.35/0.55  % (26856)Time elapsed: 0.130 s
% 1.35/0.55  % (26856)------------------------------
% 1.35/0.55  % (26856)------------------------------
% 1.49/0.59  % (26855)Refutation not found, incomplete strategy% (26855)------------------------------
% 1.49/0.59  % (26855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (26855)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.61  
% 1.49/0.61  % (26855)Memory used [KB]: 1535
% 1.49/0.61  % (26855)Time elapsed: 0.128 s
% 1.49/0.61  % (26855)------------------------------
% 1.49/0.61  % (26855)------------------------------
% 2.49/0.68  % (26842)Refutation found. Thanks to Tanya!
% 2.49/0.68  % SZS status Theorem for theBenchmark
% 2.49/0.68  % SZS output start Proof for theBenchmark
% 2.49/0.68  fof(f2042,plain,(
% 2.49/0.68    $false),
% 2.49/0.68    inference(resolution,[],[f2040,f1698])).
% 2.49/0.68  fof(f1698,plain,(
% 2.49/0.68    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 2.49/0.68    inference(superposition,[],[f33,f1659])).
% 2.49/0.68  fof(f1659,plain,(
% 2.49/0.68    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.49/0.68    inference(forward_demodulation,[],[f1641,f524])).
% 2.49/0.68  fof(f524,plain,(
% 2.49/0.68    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.49/0.68    inference(forward_demodulation,[],[f511,f115])).
% 2.49/0.68  fof(f115,plain,(
% 2.49/0.68    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)),
% 2.49/0.68    inference(resolution,[],[f108,f30])).
% 2.49/0.68  fof(f30,plain,(
% 2.49/0.68    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.49/0.68    inference(cnf_transformation,[],[f26])).
% 2.49/0.68  fof(f26,plain,(
% 2.49/0.68    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.49/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).
% 2.49/0.68  fof(f23,plain,(
% 2.49/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.49/0.68    introduced(choice_axiom,[])).
% 2.49/0.68  fof(f24,plain,(
% 2.49/0.68    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.49/0.68    introduced(choice_axiom,[])).
% 2.49/0.68  fof(f25,plain,(
% 2.49/0.68    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.49/0.68    introduced(choice_axiom,[])).
% 2.49/0.68  fof(f13,plain,(
% 2.49/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.49/0.68    inference(flattening,[],[f12])).
% 2.49/0.68  fof(f12,plain,(
% 2.49/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.49/0.68    inference(ennf_transformation,[],[f11])).
% 2.49/0.68  fof(f11,negated_conjecture,(
% 2.49/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.49/0.68    inference(negated_conjecture,[],[f10])).
% 2.49/0.68  fof(f10,conjecture,(
% 2.49/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tops_1)).
% 2.49/0.68  fof(f108,plain,(
% 2.49/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.49/0.68    inference(resolution,[],[f40,f29])).
% 2.49/0.68  fof(f29,plain,(
% 2.49/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.49/0.68    inference(cnf_transformation,[],[f26])).
% 2.49/0.68  fof(f40,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.49/0.68    inference(cnf_transformation,[],[f22])).
% 2.49/0.68  fof(f22,plain,(
% 2.49/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.68    inference(flattening,[],[f21])).
% 2.49/0.68  fof(f21,plain,(
% 2.49/0.68    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.49/0.68    inference(ennf_transformation,[],[f6])).
% 2.49/0.68  fof(f6,axiom,(
% 2.49/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.49/0.68  fof(f511,plain,(
% 2.49/0.68    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 2.49/0.68    inference(resolution,[],[f310,f29])).
% 2.49/0.68  fof(f310,plain,(
% 2.49/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2))) )),
% 2.49/0.68    inference(resolution,[],[f185,f30])).
% 2.49/0.68  fof(f185,plain,(
% 2.49/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 2.49/0.68    inference(resolution,[],[f120,f28])).
% 2.49/0.68  fof(f28,plain,(
% 2.49/0.68    l1_pre_topc(sK0)),
% 2.49/0.68    inference(cnf_transformation,[],[f26])).
% 2.49/0.68  fof(f120,plain,(
% 2.49/0.68    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,X0)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0))) )),
% 2.49/0.68    inference(resolution,[],[f32,f27])).
% 2.49/0.68  fof(f27,plain,(
% 2.49/0.68    v2_pre_topc(sK0)),
% 2.49/0.68    inference(cnf_transformation,[],[f26])).
% 2.49/0.68  fof(f32,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) )),
% 2.49/0.68    inference(cnf_transformation,[],[f15])).
% 2.49/0.68  fof(f15,plain,(
% 2.49/0.68    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.49/0.68    inference(flattening,[],[f14])).
% 2.49/0.68  fof(f14,plain,(
% 2.49/0.68    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.49/0.68    inference(ennf_transformation,[],[f9])).
% 2.49/0.68  fof(f9,axiom,(
% 2.49/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_pre_topc)).
% 2.49/0.68  fof(f1641,plain,(
% 2.49/0.68    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 2.49/0.68    inference(resolution,[],[f1622,f30])).
% 2.49/0.68  fof(f1622,plain,(
% 2.49/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X0))) )),
% 2.49/0.68    inference(resolution,[],[f722,f29])).
% 2.49/0.68  fof(f722,plain,(
% 2.49/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = k2_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))) )),
% 2.49/0.68    inference(resolution,[],[f295,f28])).
% 2.49/0.68  fof(f295,plain,(
% 2.49/0.68    ( ! [X17,X16] : (~l1_pre_topc(sK0) | k2_xboole_0(k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X16),k2_pre_topc(sK0,X17)) | ~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.49/0.68    inference(resolution,[],[f191,f36])).
% 2.49/0.68  fof(f36,plain,(
% 2.49/0.68    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.68    inference(cnf_transformation,[],[f17])).
% 2.49/0.68  fof(f17,plain,(
% 2.49/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.49/0.68    inference(flattening,[],[f16])).
% 2.49/0.68  fof(f16,plain,(
% 2.49/0.68    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.49/0.68    inference(ennf_transformation,[],[f8])).
% 2.49/0.68  fof(f8,axiom,(
% 2.49/0.68    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.49/0.68  fof(f191,plain,(
% 2.49/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(k2_pre_topc(sK0,X0),X1) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1)) )),
% 2.49/0.68    inference(resolution,[],[f112,f28])).
% 2.49/0.68  fof(f112,plain,(
% 2.49/0.68    ( ! [X6,X8,X7] : (~l1_pre_topc(X7) | k2_xboole_0(k2_pre_topc(X7,X8),X6) = k4_subset_1(u1_struct_0(X7),k2_pre_topc(X7,X8),X6) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7))) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))) )),
% 2.49/0.68    inference(resolution,[],[f40,f36])).
% 2.49/0.68  fof(f33,plain,(
% 2.49/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.49/0.68    inference(cnf_transformation,[],[f4])).
% 2.49/0.68  fof(f4,axiom,(
% 2.49/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.49/0.68  fof(f2040,plain,(
% 2.49/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 2.49/0.68    inference(forward_demodulation,[],[f2039,f34])).
% 2.49/0.68  fof(f34,plain,(
% 2.49/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.49/0.68    inference(cnf_transformation,[],[f1])).
% 2.49/0.68  fof(f1,axiom,(
% 2.49/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.49/0.68  fof(f2039,plain,(
% 2.49/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 2.49/0.68    inference(forward_demodulation,[],[f2038,f35])).
% 2.49/0.68  fof(f35,plain,(
% 2.49/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.49/0.68    inference(cnf_transformation,[],[f2])).
% 2.49/0.68  fof(f2,axiom,(
% 2.49/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.49/0.68  fof(f2038,plain,(
% 2.49/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 2.49/0.68    inference(backward_demodulation,[],[f184,f2037])).
% 2.49/0.68  fof(f2037,plain,(
% 2.49/0.68    ( ! [X0] : (k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 2.49/0.68    inference(forward_demodulation,[],[f2018,f1399])).
% 2.49/0.68  fof(f1399,plain,(
% 2.49/0.68    ( ! [X1] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X1))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X1)))) )),
% 2.49/0.68    inference(forward_demodulation,[],[f1381,f123])).
% 2.49/0.68  fof(f123,plain,(
% 2.49/0.68    ( ! [X0] : (k2_xboole_0(sK2,k4_xboole_0(sK1,X0)) = k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X0))) )),
% 2.49/0.68    inference(resolution,[],[f109,f80])).
% 2.49/0.68  fof(f80,plain,(
% 2.49/0.68    ( ! [X0] : (m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.49/0.68    inference(resolution,[],[f78,f29])).
% 2.49/0.68  fof(f78,plain,(
% 2.49/0.68    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.49/0.68    inference(superposition,[],[f37,f74])).
% 2.49/0.68  fof(f74,plain,(
% 2.49/0.68    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 2.49/0.68    inference(resolution,[],[f38,f29])).
% 2.49/0.68  fof(f38,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.49/0.68    inference(cnf_transformation,[],[f19])).
% 2.49/0.68  fof(f19,plain,(
% 2.49/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.68    inference(ennf_transformation,[],[f7])).
% 2.49/0.68  fof(f7,axiom,(
% 2.49/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.49/0.68  fof(f37,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.49/0.68    inference(cnf_transformation,[],[f18])).
% 2.49/0.68  fof(f18,plain,(
% 2.49/0.68    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.49/0.68    inference(ennf_transformation,[],[f5])).
% 2.49/0.68  fof(f5,axiom,(
% 2.49/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.49/0.68  fof(f109,plain,(
% 2.49/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK2,X1) = k4_subset_1(u1_struct_0(sK0),sK2,X1)) )),
% 2.49/0.68    inference(resolution,[],[f40,f30])).
% 2.49/0.68  fof(f1381,plain,(
% 2.49/0.68    ( ! [X1] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X1))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,k4_xboole_0(sK1,X1)))) )),
% 2.49/0.68    inference(resolution,[],[f311,f30])).
% 2.49/0.68  fof(f311,plain,(
% 2.49/0.68    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X2),k2_pre_topc(sK0,k4_xboole_0(sK1,X3))) = k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X2,k4_xboole_0(sK1,X3)))) )),
% 2.49/0.68    inference(resolution,[],[f185,f80])).
% 2.49/0.68  fof(f2018,plain,(
% 2.49/0.68    ( ! [X0] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0))) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X0)))) )),
% 2.49/0.68    inference(resolution,[],[f1623,f80])).
% 2.49/0.68  fof(f1623,plain,(
% 2.49/0.68    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,X1))) )),
% 2.49/0.68    inference(resolution,[],[f722,f30])).
% 2.49/0.68  fof(f184,plain,(
% 2.49/0.68    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 2.49/0.68    inference(resolution,[],[f183,f39])).
% 2.49/0.68  fof(f39,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.49/0.68    inference(cnf_transformation,[],[f20])).
% 2.49/0.68  fof(f20,plain,(
% 2.49/0.68    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.49/0.68    inference(ennf_transformation,[],[f3])).
% 2.49/0.68  fof(f3,axiom,(
% 2.49/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.49/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.49/0.68  fof(f183,plain,(
% 2.49/0.68    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 2.49/0.68    inference(backward_demodulation,[],[f77,f175])).
% 2.49/0.68  fof(f175,plain,(
% 2.49/0.68    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 2.49/0.68    inference(resolution,[],[f152,f29])).
% 2.49/0.68  fof(f152,plain,(
% 2.49/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)) )),
% 2.49/0.68    inference(resolution,[],[f92,f28])).
% 2.49/0.68  fof(f92,plain,(
% 2.49/0.68    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2)) )),
% 2.49/0.68    inference(resolution,[],[f36,f38])).
% 2.49/0.68  fof(f77,plain,(
% 2.49/0.68    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 2.49/0.68    inference(backward_demodulation,[],[f31,f74])).
% 2.49/0.68  fof(f31,plain,(
% 2.49/0.68    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 2.49/0.68    inference(cnf_transformation,[],[f26])).
% 2.49/0.68  % SZS output end Proof for theBenchmark
% 2.49/0.68  % (26842)------------------------------
% 2.49/0.68  % (26842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.68  % (26842)Termination reason: Refutation
% 2.49/0.68  
% 2.49/0.68  % (26842)Memory used [KB]: 4477
% 2.49/0.68  % (26842)Time elapsed: 0.252 s
% 2.49/0.68  % (26842)------------------------------
% 2.49/0.68  % (26842)------------------------------
% 2.49/0.68  % (26832)Success in time 0.323 s
%------------------------------------------------------------------------------
