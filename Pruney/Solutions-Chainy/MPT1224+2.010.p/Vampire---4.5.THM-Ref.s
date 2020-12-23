%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:53 EST 2020

% Result     : Theorem 3.27s
% Output     : Refutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 644 expanded)
%              Number of leaves         :   16 ( 222 expanded)
%              Depth                    :   20
%              Number of atoms          :  231 (2525 expanded)
%              Number of equality atoms :   54 ( 115 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3435,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3429,f1605])).

fof(f1605,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f1604,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1604,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f1599,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1599,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)))) ),
    inference(backward_demodulation,[],[f130,f1597])).

fof(f1597,plain,(
    ! [X17] : k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X17))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X17))) ),
    inference(forward_demodulation,[],[f1596,f328])).

fof(f328,plain,(
    ! [X3] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X3)),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X3))) ),
    inference(backward_demodulation,[],[f316,f327])).

fof(f327,plain,(
    ! [X5] : k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X5),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK1,X5)) ),
    inference(forward_demodulation,[],[f318,f40])).

fof(f318,plain,(
    ! [X5] : k2_xboole_0(k4_xboole_0(sK1,X5),sK2) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X5),sK2) ),
    inference(resolution,[],[f117,f72])).

fof(f72,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X3,sK2) = k4_subset_1(u1_struct_0(sK0),X3,sK2) ) ),
    inference(resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).

fof(f117,plain,(
    ! [X3] : m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f83,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f83,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f61,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f316,plain,(
    ! [X3] : k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X3),sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X3)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2)) ) ),
    inference(subsumption_resolution,[],[f78,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f36,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).

fof(f1596,plain,(
    ! [X17] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X17))) ),
    inference(forward_demodulation,[],[f1582,f40])).

fof(f1582,plain,(
    ! [X17] : k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f472,f919])).

fof(f919,plain,(
    ! [X32] : r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X32)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f258,f44])).

fof(f258,plain,(
    ! [X6] : m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X6)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f119,f83])).

fof(f119,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f34,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f472,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k2_xboole_0(X0,k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f107,f45])).

fof(f107,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_xboole_0(X3,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2)) ) ),
    inference(resolution,[],[f75,f50])).

fof(f75,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f36,f43])).

fof(f130,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f82,plain,(
    ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f81,f62])).

fof(f62,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f55,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f35,f43])).

fof(f81,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f67,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f67,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f37,f60])).

fof(f60,plain,(
    ! [X4] : k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4) ),
    inference(resolution,[],[f35,f47])).

fof(f37,plain,(
    ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3429,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f3133,f391])).

fof(f391,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f390,f75])).

fof(f390,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f386,f62])).

fof(f386,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f362,f50])).

fof(f362,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f159,f361])).

fof(f361,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f360,f308])).

fof(f308,plain,(
    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f307,f62])).

fof(f307,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f298,f75])).

fof(f298,plain,
    ( k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f181,f50])).

fof(f181,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f176,f140])).

fof(f140,plain,(
    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) ),
    inference(resolution,[],[f72,f35])).

fof(f176,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(resolution,[],[f79,f35])).

fof(f360,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(forward_demodulation,[],[f359,f40])).

fof(f359,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f358,f75])).

fof(f358,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f356,f62])).

fof(f356,plain,
    ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f159,f50])).

fof(f159,plain,(
    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f66,f36])).

fof(f66,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f65,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f57,f34])).

fof(f57,plain,(
    ! [X1] :
      ( k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f35,f38])).

fof(f3133,plain,(
    ! [X8,X7] : r1_tarski(X7,k2_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f3094,f41])).

fof(f3094,plain,(
    ! [X8,X7] : r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(resolution,[],[f2959,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f2959,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f39,f1637])).

fof(f1637,plain,(
    ! [X4] : k4_xboole_0(X4,k4_xboole_0(sK1,u1_struct_0(sK0))) = X4 ),
    inference(forward_demodulation,[],[f1618,f267])).

fof(f267,plain,(
    ! [X4] : k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X4) = X4 ),
    inference(resolution,[],[f237,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f237,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,u1_struct_0(sK0)),X0) ),
    inference(resolution,[],[f170,f48])).

fof(f170,plain,(
    ! [X1] : r1_tarski(sK1,k2_xboole_0(u1_struct_0(sK0),X1)) ),
    inference(superposition,[],[f115,f40])).

fof(f115,plain,(
    ! [X0] : r1_tarski(sK1,k2_xboole_0(X0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f83,f49])).

fof(f1618,plain,(
    ! [X4] : k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X4) = k4_xboole_0(X4,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(superposition,[],[f267,f41])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:40:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (28299)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (28300)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (28309)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (28304)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (28310)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.51  % (28291)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (28303)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (28288)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (28287)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (28289)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.51  % (28302)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (28292)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (28293)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (28310)Refutation not found, incomplete strategy% (28310)------------------------------
% 0.21/0.51  % (28310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (28310)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (28310)Memory used [KB]: 10618
% 0.21/0.51  % (28310)Time elapsed: 0.053 s
% 0.21/0.51  % (28310)------------------------------
% 0.21/0.51  % (28310)------------------------------
% 0.21/0.52  % (28294)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (28297)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.52  % (28296)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.53  % (28290)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.53  % (28295)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.53  % (28290)Refutation not found, incomplete strategy% (28290)------------------------------
% 0.21/0.53  % (28290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28290)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28290)Memory used [KB]: 10490
% 0.21/0.53  % (28290)Time elapsed: 0.113 s
% 0.21/0.53  % (28290)------------------------------
% 0.21/0.53  % (28290)------------------------------
% 0.21/0.53  % (28306)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (28305)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (28308)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (28307)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.54  % (28298)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.55  % (28301)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.78/0.61  % (28309)Refutation not found, incomplete strategy% (28309)------------------------------
% 1.78/0.61  % (28309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (28309)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (28309)Memory used [KB]: 1663
% 1.78/0.61  % (28309)Time elapsed: 0.196 s
% 1.78/0.61  % (28309)------------------------------
% 1.78/0.61  % (28309)------------------------------
% 3.27/0.82  % (28298)Refutation found. Thanks to Tanya!
% 3.27/0.82  % SZS status Theorem for theBenchmark
% 3.27/0.82  % SZS output start Proof for theBenchmark
% 3.27/0.82  fof(f3435,plain,(
% 3.27/0.82    $false),
% 3.27/0.82    inference(subsumption_resolution,[],[f3429,f1605])).
% 3.27/0.82  fof(f1605,plain,(
% 3.27/0.82    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 3.27/0.82    inference(forward_demodulation,[],[f1604,f40])).
% 3.27/0.82  fof(f40,plain,(
% 3.27/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.27/0.82    inference(cnf_transformation,[],[f1])).
% 3.27/0.82  fof(f1,axiom,(
% 3.27/0.82    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.27/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.27/0.82  fof(f1604,plain,(
% 3.27/0.82    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,sK1)))),
% 3.27/0.82    inference(forward_demodulation,[],[f1599,f41])).
% 3.27/0.83  fof(f41,plain,(
% 3.27/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.27/0.83    inference(cnf_transformation,[],[f5])).
% 3.27/0.83  fof(f5,axiom,(
% 3.27/0.83    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.27/0.83  fof(f1599,plain,(
% 3.27/0.83    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))))),
% 3.27/0.83    inference(backward_demodulation,[],[f130,f1597])).
% 3.27/0.83  fof(f1597,plain,(
% 3.27/0.83    ( ! [X17] : (k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X17))) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X17)))) )),
% 3.27/0.83    inference(forward_demodulation,[],[f1596,f328])).
% 3.27/0.83  fof(f328,plain,(
% 3.27/0.83    ( ! [X3] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X3)),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK2,k4_xboole_0(sK1,X3)))) )),
% 3.27/0.83    inference(backward_demodulation,[],[f316,f327])).
% 3.27/0.83  fof(f327,plain,(
% 3.27/0.83    ( ! [X5] : (k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X5),sK2) = k2_xboole_0(sK2,k4_xboole_0(sK1,X5))) )),
% 3.27/0.83    inference(forward_demodulation,[],[f318,f40])).
% 3.27/0.83  fof(f318,plain,(
% 3.27/0.83    ( ! [X5] : (k2_xboole_0(k4_xboole_0(sK1,X5),sK2) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X5),sK2)) )),
% 3.27/0.83    inference(resolution,[],[f117,f72])).
% 3.27/0.83  fof(f72,plain,(
% 3.27/0.83    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X3,sK2) = k4_subset_1(u1_struct_0(sK0),X3,sK2)) )),
% 3.27/0.83    inference(resolution,[],[f36,f50])).
% 3.27/0.83  fof(f50,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.27/0.83    inference(cnf_transformation,[],[f27])).
% 3.27/0.83  fof(f27,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.27/0.83    inference(flattening,[],[f26])).
% 3.27/0.83  fof(f26,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.27/0.83    inference(ennf_transformation,[],[f8])).
% 3.27/0.83  fof(f8,axiom,(
% 3.27/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.27/0.83  fof(f36,plain,(
% 3.27/0.83    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(cnf_transformation,[],[f31])).
% 3.27/0.83  fof(f31,plain,(
% 3.27/0.83    ((~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.27/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f30,f29,f28])).
% 3.27/0.83  fof(f28,plain,(
% 3.27/0.83    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.27/0.83    introduced(choice_axiom,[])).
% 3.27/0.83  fof(f29,plain,(
% 3.27/0.83    ? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.27/0.83    introduced(choice_axiom,[])).
% 3.27/0.83  fof(f30,plain,(
% 3.27/0.83    ? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.27/0.83    introduced(choice_axiom,[])).
% 3.27/0.83  fof(f16,plain,(
% 3.27/0.83    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.27/0.83    inference(flattening,[],[f15])).
% 3.27/0.83  fof(f15,plain,(
% 3.27/0.83    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.27/0.83    inference(ennf_transformation,[],[f14])).
% 3.27/0.83  fof(f14,negated_conjecture,(
% 3.27/0.83    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.27/0.83    inference(negated_conjecture,[],[f13])).
% 3.27/0.83  fof(f13,conjecture,(
% 3.27/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)),k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),X1,X2))))))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_1)).
% 3.27/0.83  fof(f117,plain,(
% 3.27/0.83    ( ! [X3] : (m1_subset_1(k4_xboole_0(sK1,X3),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(resolution,[],[f83,f45])).
% 3.27/0.83  fof(f45,plain,(
% 3.27/0.83    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f32])).
% 3.27/0.83  fof(f32,plain,(
% 3.27/0.83    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.27/0.83    inference(nnf_transformation,[],[f10])).
% 3.27/0.83  fof(f10,axiom,(
% 3.27/0.83    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.27/0.83  fof(f83,plain,(
% 3.27/0.83    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 3.27/0.83    inference(resolution,[],[f61,f46])).
% 3.27/0.83  fof(f46,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f22])).
% 3.27/0.83  fof(f22,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.27/0.83    inference(ennf_transformation,[],[f2])).
% 3.27/0.83  fof(f2,axiom,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 3.27/0.83  fof(f61,plain,(
% 3.27/0.83    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.27/0.83    inference(resolution,[],[f35,f44])).
% 3.27/0.83  fof(f44,plain,(
% 3.27/0.83    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.27/0.83    inference(cnf_transformation,[],[f32])).
% 3.27/0.83  fof(f35,plain,(
% 3.27/0.83    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(cnf_transformation,[],[f31])).
% 3.27/0.83  fof(f316,plain,(
% 3.27/0.83    ( ! [X3] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),k4_xboole_0(sK1,X3),sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X3)),k2_pre_topc(sK0,sK2))) )),
% 3.27/0.83    inference(resolution,[],[f117,f79])).
% 3.27/0.83  fof(f79,plain,(
% 3.27/0.83    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2))) )),
% 3.27/0.83    inference(subsumption_resolution,[],[f78,f33])).
% 3.27/0.83  fof(f33,plain,(
% 3.27/0.83    v2_pre_topc(sK0)),
% 3.27/0.83    inference(cnf_transformation,[],[f31])).
% 3.27/0.83  fof(f78,plain,(
% 3.27/0.83    ( ! [X1] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 3.27/0.83    inference(subsumption_resolution,[],[f70,f34])).
% 3.27/0.83  fof(f34,plain,(
% 3.27/0.83    l1_pre_topc(sK0)),
% 3.27/0.83    inference(cnf_transformation,[],[f31])).
% 3.27/0.83  fof(f70,plain,(
% 3.27/0.83    ( ! [X1] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 3.27/0.83    inference(resolution,[],[f36,f38])).
% 3.27/0.83  fof(f38,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f18])).
% 3.27/0.83  fof(f18,plain,(
% 3.27/0.83    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.27/0.83    inference(flattening,[],[f17])).
% 3.27/0.83  fof(f17,plain,(
% 3.27/0.83    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.27/0.83    inference(ennf_transformation,[],[f12])).
% 3.27/0.83  fof(f12,axiom,(
% 3.27/0.83    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,k4_subset_1(u1_struct_0(X0),X1,X2)) = k4_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_pre_topc)).
% 3.27/0.83  fof(f1596,plain,(
% 3.27/0.83    ( ! [X17] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,X17)))) )),
% 3.27/0.83    inference(forward_demodulation,[],[f1582,f40])).
% 3.27/0.83  fof(f1582,plain,(
% 3.27/0.83    ( ! [X17] : (k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2)) = k2_xboole_0(k2_pre_topc(sK0,k4_xboole_0(sK1,X17)),k2_pre_topc(sK0,sK2))) )),
% 3.27/0.83    inference(resolution,[],[f472,f919])).
% 3.27/0.83  fof(f919,plain,(
% 3.27/0.83    ( ! [X32] : (r1_tarski(k2_pre_topc(sK0,k4_xboole_0(sK1,X32)),u1_struct_0(sK0))) )),
% 3.27/0.83    inference(resolution,[],[f258,f44])).
% 3.27/0.83  fof(f258,plain,(
% 3.27/0.83    ( ! [X6] : (m1_subset_1(k2_pre_topc(sK0,k4_xboole_0(sK1,X6)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(resolution,[],[f119,f83])).
% 3.27/0.83  fof(f119,plain,(
% 3.27/0.83    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(resolution,[],[f53,f45])).
% 3.27/0.83  fof(f53,plain,(
% 3.27/0.83    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(resolution,[],[f34,f43])).
% 3.27/0.83  fof(f43,plain,(
% 3.27/0.83    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f21])).
% 3.27/0.83  fof(f21,plain,(
% 3.27/0.83    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.27/0.83    inference(flattening,[],[f20])).
% 3.27/0.83  fof(f20,plain,(
% 3.27/0.83    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.27/0.83    inference(ennf_transformation,[],[f11])).
% 3.27/0.83  fof(f11,axiom,(
% 3.27/0.83    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 3.27/0.83  fof(f472,plain,(
% 3.27/0.83    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | k4_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k2_xboole_0(X0,k2_pre_topc(sK0,sK2))) )),
% 3.27/0.83    inference(resolution,[],[f107,f45])).
% 3.27/0.83  fof(f107,plain,(
% 3.27/0.83    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X3,k2_pre_topc(sK0,sK2)) = k4_subset_1(u1_struct_0(sK0),X3,k2_pre_topc(sK0,sK2))) )),
% 3.27/0.83    inference(resolution,[],[f75,f50])).
% 3.27/0.83  fof(f75,plain,(
% 3.27/0.83    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f68,f34])).
% 3.27/0.83  fof(f68,plain,(
% 3.27/0.83    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.27/0.83    inference(resolution,[],[f36,f43])).
% 3.27/0.83  fof(f130,plain,(
% 3.27/0.83    ~r1_tarski(k2_pre_topc(sK0,sK1),k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))))),
% 3.27/0.83    inference(resolution,[],[f82,f48])).
% 3.27/0.83  fof(f48,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 3.27/0.83    inference(cnf_transformation,[],[f24])).
% 3.27/0.83  fof(f24,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.27/0.83    inference(ennf_transformation,[],[f6])).
% 3.27/0.83  fof(f6,axiom,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.27/0.83  fof(f82,plain,(
% 3.27/0.83    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f81,f62])).
% 3.27/0.83  fof(f62,plain,(
% 3.27/0.83    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f55,f34])).
% 3.27/0.83  fof(f55,plain,(
% 3.27/0.83    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.27/0.83    inference(resolution,[],[f35,f43])).
% 3.27/0.83  fof(f81,plain,(
% 3.27/0.83    ~r1_tarski(k4_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(superposition,[],[f67,f47])).
% 3.27/0.83  fof(f47,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.27/0.83    inference(cnf_transformation,[],[f23])).
% 3.27/0.83  fof(f23,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.27/0.83    inference(ennf_transformation,[],[f9])).
% 3.27/0.83  fof(f9,axiom,(
% 3.27/0.83    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.27/0.83  fof(f67,plain,(
% 3.27/0.83    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k4_xboole_0(sK1,sK2)))),
% 3.27/0.83    inference(backward_demodulation,[],[f37,f60])).
% 3.27/0.83  fof(f60,plain,(
% 3.27/0.83    ( ! [X4] : (k7_subset_1(u1_struct_0(sK0),sK1,X4) = k4_xboole_0(sK1,X4)) )),
% 3.27/0.83    inference(resolution,[],[f35,f47])).
% 3.27/0.83  fof(f37,plain,(
% 3.27/0.83    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)))),
% 3.27/0.83    inference(cnf_transformation,[],[f31])).
% 3.27/0.83  fof(f3429,plain,(
% 3.27/0.83    r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)))),
% 3.27/0.83    inference(superposition,[],[f3133,f391])).
% 3.27/0.83  fof(f391,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))),
% 3.27/0.83    inference(subsumption_resolution,[],[f390,f75])).
% 3.27/0.83  fof(f390,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f386,f62])).
% 3.27/0.83  fof(f386,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(superposition,[],[f362,f50])).
% 3.27/0.83  fof(f362,plain,(
% 3.27/0.83    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))),
% 3.27/0.83    inference(backward_demodulation,[],[f159,f361])).
% 3.27/0.83  fof(f361,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))),
% 3.27/0.83    inference(forward_demodulation,[],[f360,f308])).
% 3.27/0.83  fof(f308,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 3.27/0.83    inference(subsumption_resolution,[],[f307,f62])).
% 3.27/0.83  fof(f307,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f298,f75])).
% 3.27/0.83  fof(f298,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(superposition,[],[f181,f50])).
% 3.27/0.83  fof(f181,plain,(
% 3.27/0.83    k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) = k2_pre_topc(sK0,k2_xboole_0(sK1,sK2))),
% 3.27/0.83    inference(forward_demodulation,[],[f176,f140])).
% 3.27/0.83  fof(f140,plain,(
% 3.27/0.83    k2_xboole_0(sK1,sK2) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)),
% 3.27/0.83    inference(resolution,[],[f72,f35])).
% 3.27/0.83  fof(f176,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK1,sK2)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 3.27/0.83    inference(resolution,[],[f79,f35])).
% 3.27/0.83  fof(f360,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 3.27/0.83    inference(forward_demodulation,[],[f359,f40])).
% 3.27/0.83  fof(f359,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))),
% 3.27/0.83    inference(subsumption_resolution,[],[f358,f75])).
% 3.27/0.83  fof(f358,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(subsumption_resolution,[],[f356,f62])).
% 3.27/0.83  fof(f356,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_xboole_0(k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.27/0.83    inference(superposition,[],[f159,f50])).
% 3.27/0.83  fof(f159,plain,(
% 3.27/0.83    k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),sK2,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK2),k2_pre_topc(sK0,sK1))),
% 3.27/0.83    inference(resolution,[],[f66,f36])).
% 3.27/0.83  fof(f66,plain,(
% 3.27/0.83    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1))) )),
% 3.27/0.83    inference(subsumption_resolution,[],[f65,f33])).
% 3.27/0.83  fof(f65,plain,(
% 3.27/0.83    ( ! [X1] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 3.27/0.83    inference(subsumption_resolution,[],[f57,f34])).
% 3.27/0.83  fof(f57,plain,(
% 3.27/0.83    ( ! [X1] : (k2_pre_topc(sK0,k4_subset_1(u1_struct_0(sK0),X1,sK1)) = k4_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 3.27/0.83    inference(resolution,[],[f35,f38])).
% 3.27/0.83  fof(f3133,plain,(
% 3.27/0.83    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(X8,X7))) )),
% 3.27/0.83    inference(forward_demodulation,[],[f3094,f41])).
% 3.27/0.83  fof(f3094,plain,(
% 3.27/0.83    ( ! [X8,X7] : (r1_tarski(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 3.27/0.83    inference(resolution,[],[f2959,f49])).
% 3.27/0.83  fof(f49,plain,(
% 3.27/0.83    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f25])).
% 3.27/0.83  fof(f25,plain,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.27/0.83    inference(ennf_transformation,[],[f7])).
% 3.27/0.83  fof(f7,axiom,(
% 3.27/0.83    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 3.27/0.83  fof(f2959,plain,(
% 3.27/0.83    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.27/0.83    inference(superposition,[],[f39,f1637])).
% 3.27/0.83  fof(f1637,plain,(
% 3.27/0.83    ( ! [X4] : (k4_xboole_0(X4,k4_xboole_0(sK1,u1_struct_0(sK0))) = X4) )),
% 3.27/0.83    inference(forward_demodulation,[],[f1618,f267])).
% 3.27/0.83  fof(f267,plain,(
% 3.27/0.83    ( ! [X4] : (k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X4) = X4) )),
% 3.27/0.83    inference(resolution,[],[f237,f42])).
% 3.27/0.83  fof(f42,plain,(
% 3.27/0.83    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f19])).
% 3.27/0.83  fof(f19,plain,(
% 3.27/0.83    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.27/0.83    inference(ennf_transformation,[],[f3])).
% 3.27/0.83  fof(f3,axiom,(
% 3.27/0.83    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.27/0.83  fof(f237,plain,(
% 3.27/0.83    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,u1_struct_0(sK0)),X0)) )),
% 3.27/0.83    inference(resolution,[],[f170,f48])).
% 3.27/0.83  fof(f170,plain,(
% 3.27/0.83    ( ! [X1] : (r1_tarski(sK1,k2_xboole_0(u1_struct_0(sK0),X1))) )),
% 3.27/0.83    inference(superposition,[],[f115,f40])).
% 3.27/0.83  fof(f115,plain,(
% 3.27/0.83    ( ! [X0] : (r1_tarski(sK1,k2_xboole_0(X0,u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(resolution,[],[f83,f49])).
% 3.27/0.83  fof(f1618,plain,(
% 3.27/0.83    ( ! [X4] : (k2_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X4) = k4_xboole_0(X4,k4_xboole_0(sK1,u1_struct_0(sK0)))) )),
% 3.27/0.83    inference(superposition,[],[f267,f41])).
% 3.27/0.83  fof(f39,plain,(
% 3.27/0.83    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.27/0.83    inference(cnf_transformation,[],[f4])).
% 3.27/0.83  fof(f4,axiom,(
% 3.27/0.83    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.27/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.27/0.83  % SZS output end Proof for theBenchmark
% 3.27/0.83  % (28298)------------------------------
% 3.27/0.83  % (28298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.27/0.83  % (28298)Termination reason: Refutation
% 3.27/0.83  
% 3.27/0.83  % (28298)Memory used [KB]: 3709
% 3.27/0.83  % (28298)Time elapsed: 0.378 s
% 3.27/0.83  % (28298)------------------------------
% 3.27/0.83  % (28298)------------------------------
% 3.27/0.83  % (28286)Success in time 0.464 s
%------------------------------------------------------------------------------
