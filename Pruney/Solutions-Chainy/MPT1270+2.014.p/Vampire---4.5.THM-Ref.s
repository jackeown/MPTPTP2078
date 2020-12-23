%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:37 EST 2020

% Result     : Theorem 2.39s
% Output     : Refutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 491 expanded)
%              Number of leaves         :   19 ( 130 expanded)
%              Depth                    :   18
%              Number of atoms          :  300 (1950 expanded)
%              Number of equality atoms :   64 ( 210 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6872,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6871,f6686])).

fof(f6686,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f6685,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f6685,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f6684,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f6684,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f6674,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f66,f49])).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f6674,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f157,f6632])).

fof(f6632,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f6631])).

fof(f6631,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(forward_demodulation,[],[f6577,f960])).

fof(f960,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f362,f383])).

fof(f383,plain,(
    ! [X8] : r1_xboole_0(k4_xboole_0(X8,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f306,f212])).

fof(f212,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f188,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f188,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f132,f46])).

fof(f132,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f306,plain,(
    ! [X12,X10,X11] : r1_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X12)),X11) ),
    inference(resolution,[],[f300,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f300,plain,(
    ! [X4,X3] : r1_xboole_0(k4_xboole_0(X4,X3),X3) ),
    inference(superposition,[],[f282,f200])).

fof(f200,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f98,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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

fof(f98,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k4_xboole_0(X4,k4_xboole_0(X6,X5)) = X4 ) ),
    inference(resolution,[],[f71,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f282,plain,(
    ! [X2,X3] : r1_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,(
    ! [X2,X3] :
      ( X2 != X2
      | r1_xboole_0(X2,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f65,f200])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f362,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,X1),X0)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f168,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f168,plain,(
    ! [X6,X8,X7] :
      ( r1_xboole_0(X8,k4_xboole_0(X6,X7))
      | ~ r1_xboole_0(X8,X6) ) ),
    inference(superposition,[],[f69,f83])).

fof(f83,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f59,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f6577,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f200,f1727])).

fof(f1727,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(superposition,[],[f463,f608])).

fof(f608,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f324,f46])).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f145,f45])).

fof(f145,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | k1_tops_1(X3,X2) = k4_xboole_0(k1_tops_1(X3,X2),k2_tops_1(X3,X2)) ) ),
    inference(resolution,[],[f54,f64])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).

fof(f463,plain,(
    ! [X0] :
      ( sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1)))
      | k1_xboole_0 = k1_tops_1(sK0,sK1) ) ),
    inference(resolution,[],[f206,f243])).

fof(f243,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f154,f46])).

fof(f154,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tops_1(X0,sK0)
      | k1_xboole_0 = k1_tops_1(sK0,X0) ) ),
    inference(resolution,[],[f56,f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f206,plain,(
    ! [X10] :
      ( v2_tops_1(sK1,sK0)
      | sK1 = k4_xboole_0(sK1,k4_xboole_0(X10,k2_tops_1(sK0,sK1))) ) ),
    inference(resolution,[],[f98,f47])).

fof(f47,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,X1),k1_xboole_0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f155,f78])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,X1),k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,k1_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(extensionality_resolution,[],[f63,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6871,plain,(
    ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f6849,f180])).

fof(f180,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f131,f46])).

fof(f131,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ) ),
    inference(resolution,[],[f52,f45])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f6849,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(superposition,[],[f48,f6683])).

fof(f6683,plain,(
    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f6664,f115])).

fof(f115,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(resolution,[],[f100,f64])).

fof(f100,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f97,f75])).

fof(f97,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | r1_xboole_0(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f71,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | r1_xboole_0(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f69,f84])).

fof(f84,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3 ),
    inference(resolution,[],[f59,f78])).

fof(f6664,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[],[f1525,f6632])).

fof(f1525,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f671,f316])).

fof(f316,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f162,f46])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f671,plain,(
    ! [X5] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5) ),
    inference(resolution,[],[f329,f46])).

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1) ) ),
    inference(resolution,[],[f146,f45])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2) ) ),
    inference(resolution,[],[f60,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f48,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:52:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (29284)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.47  % (29292)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (29300)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (29299)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (29291)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (29287)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (29304)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (29280)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (29280)Refutation not found, incomplete strategy% (29280)------------------------------
% 0.21/0.53  % (29280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (29285)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (29296)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (29280)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (29280)Memory used [KB]: 10618
% 0.21/0.53  % (29280)Time elapsed: 0.082 s
% 0.21/0.53  % (29280)------------------------------
% 0.21/0.53  % (29280)------------------------------
% 0.21/0.54  % (29291)Refutation not found, incomplete strategy% (29291)------------------------------
% 0.21/0.54  % (29291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29291)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29291)Memory used [KB]: 10746
% 0.21/0.54  % (29291)Time elapsed: 0.142 s
% 0.21/0.54  % (29291)------------------------------
% 0.21/0.54  % (29291)------------------------------
% 0.21/0.54  % (29283)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.55  % (29293)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (29293)Refutation not found, incomplete strategy% (29293)------------------------------
% 0.21/0.55  % (29293)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29293)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29293)Memory used [KB]: 6268
% 0.21/0.55  % (29293)Time elapsed: 0.103 s
% 0.21/0.55  % (29293)------------------------------
% 0.21/0.55  % (29293)------------------------------
% 0.21/0.55  % (29303)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (29281)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (29295)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.57  % (29305)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (29286)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.57  % (29294)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.57  % (29297)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.58  % (29282)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.58  % (29289)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.58  % (29302)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.59  % (29301)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.59  % (29288)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.59  % (29298)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.61  % (29290)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 2.39/0.68  % (29281)Refutation not found, incomplete strategy% (29281)------------------------------
% 2.39/0.68  % (29281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.68  % (29281)Termination reason: Refutation not found, incomplete strategy
% 2.39/0.68  
% 2.39/0.68  % (29281)Memory used [KB]: 11385
% 2.39/0.68  % (29281)Time elapsed: 0.250 s
% 2.39/0.68  % (29281)------------------------------
% 2.39/0.68  % (29281)------------------------------
% 2.39/0.70  % (29296)Refutation found. Thanks to Tanya!
% 2.39/0.70  % SZS status Theorem for theBenchmark
% 2.39/0.70  % SZS output start Proof for theBenchmark
% 2.39/0.70  fof(f6872,plain,(
% 2.39/0.70    $false),
% 2.39/0.70    inference(subsumption_resolution,[],[f6871,f6686])).
% 2.39/0.70  fof(f6686,plain,(
% 2.39/0.70    v2_tops_1(sK1,sK0)),
% 2.39/0.70    inference(subsumption_resolution,[],[f6685,f45])).
% 2.39/0.70  fof(f45,plain,(
% 2.39/0.70    l1_pre_topc(sK0)),
% 2.39/0.70    inference(cnf_transformation,[],[f39])).
% 2.39/0.70  fof(f39,plain,(
% 2.39/0.70    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 2.39/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 2.39/0.70  fof(f37,plain,(
% 2.39/0.70    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 2.39/0.70    introduced(choice_axiom,[])).
% 2.39/0.70  fof(f38,plain,(
% 2.39/0.70    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.39/0.70    introduced(choice_axiom,[])).
% 2.39/0.70  fof(f36,plain,(
% 2.39/0.70    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.39/0.70    inference(flattening,[],[f35])).
% 2.39/0.70  fof(f35,plain,(
% 2.39/0.70    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.39/0.70    inference(nnf_transformation,[],[f20])).
% 2.39/0.70  fof(f20,plain,(
% 2.39/0.70    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f19])).
% 2.39/0.70  fof(f19,negated_conjecture,(
% 2.39/0.70    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.39/0.70    inference(negated_conjecture,[],[f18])).
% 2.39/0.70  fof(f18,conjecture,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 2.39/0.70  fof(f6685,plain,(
% 2.39/0.70    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 2.39/0.70    inference(subsumption_resolution,[],[f6684,f46])).
% 2.39/0.70  fof(f46,plain,(
% 2.39/0.70    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.39/0.70    inference(cnf_transformation,[],[f39])).
% 2.39/0.70  fof(f6684,plain,(
% 2.39/0.70    v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.39/0.70    inference(subsumption_resolution,[],[f6674,f78])).
% 2.39/0.70  fof(f78,plain,(
% 2.39/0.70    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.39/0.70    inference(resolution,[],[f66,f49])).
% 2.39/0.70  fof(f49,plain,(
% 2.39/0.70    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.39/0.70    inference(cnf_transformation,[],[f9])).
% 2.39/0.70  fof(f9,axiom,(
% 2.39/0.70    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 2.39/0.70  fof(f66,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f44])).
% 2.39/0.70  fof(f44,plain,(
% 2.39/0.70    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.39/0.70    inference(nnf_transformation,[],[f10])).
% 2.39/0.70  fof(f10,axiom,(
% 2.39/0.70    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.39/0.70  fof(f6674,plain,(
% 2.39/0.70    ~r1_tarski(k1_xboole_0,k1_xboole_0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.39/0.70    inference(superposition,[],[f157,f6632])).
% 2.39/0.70  fof(f6632,plain,(
% 2.39/0.70    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.39/0.70    inference(duplicate_literal_removal,[],[f6631])).
% 2.39/0.70  fof(f6631,plain,(
% 2.39/0.70    k1_xboole_0 = k1_tops_1(sK0,sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.39/0.70    inference(forward_demodulation,[],[f6577,f960])).
% 2.39/0.70  fof(f960,plain,(
% 2.39/0.70    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.39/0.70    inference(resolution,[],[f362,f383])).
% 2.39/0.70  fof(f383,plain,(
% 2.39/0.70    ( ! [X8] : (r1_xboole_0(k4_xboole_0(X8,sK1),k1_tops_1(sK0,sK1))) )),
% 2.39/0.70    inference(superposition,[],[f306,f212])).
% 2.39/0.70  fof(f212,plain,(
% 2.39/0.70    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.39/0.70    inference(resolution,[],[f188,f59])).
% 2.39/0.70  fof(f59,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.39/0.70    inference(cnf_transformation,[],[f27])).
% 2.39/0.70  fof(f27,plain,(
% 2.39/0.70    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.39/0.70    inference(ennf_transformation,[],[f2])).
% 2.39/0.70  fof(f2,axiom,(
% 2.39/0.70    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.39/0.70  fof(f188,plain,(
% 2.39/0.70    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.39/0.70    inference(resolution,[],[f132,f46])).
% 2.39/0.70  fof(f132,plain,(
% 2.39/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.39/0.70    inference(resolution,[],[f53,f45])).
% 2.39/0.70  fof(f53,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f23])).
% 2.39/0.70  fof(f23,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f15])).
% 2.39/0.70  fof(f15,axiom,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.39/0.70  fof(f306,plain,(
% 2.39/0.70    ( ! [X12,X10,X11] : (r1_xboole_0(k4_xboole_0(X10,k2_xboole_0(X11,X12)),X11)) )),
% 2.39/0.70    inference(resolution,[],[f300,f69])).
% 2.39/0.70  fof(f69,plain,(
% 2.39/0.70    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f30])).
% 2.39/0.70  fof(f30,plain,(
% 2.39/0.70    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.39/0.70    inference(ennf_transformation,[],[f5])).
% 2.39/0.70  fof(f5,axiom,(
% 2.39/0.70    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.39/0.70  fof(f300,plain,(
% 2.39/0.70    ( ! [X4,X3] : (r1_xboole_0(k4_xboole_0(X4,X3),X3)) )),
% 2.39/0.70    inference(superposition,[],[f282,f200])).
% 2.39/0.70  fof(f200,plain,(
% 2.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.39/0.70    inference(resolution,[],[f98,f75])).
% 2.39/0.70  fof(f75,plain,(
% 2.39/0.70    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.39/0.70    inference(equality_resolution,[],[f62])).
% 2.39/0.70  fof(f62,plain,(
% 2.39/0.70    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.39/0.70    inference(cnf_transformation,[],[f42])).
% 2.39/0.70  fof(f42,plain,(
% 2.39/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/0.70    inference(flattening,[],[f41])).
% 2.39/0.70  fof(f41,plain,(
% 2.39/0.70    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.39/0.70    inference(nnf_transformation,[],[f1])).
% 2.39/0.70  fof(f1,axiom,(
% 2.39/0.70    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.39/0.70  fof(f98,plain,(
% 2.39/0.70    ( ! [X6,X4,X5] : (~r1_tarski(X4,X5) | k4_xboole_0(X4,k4_xboole_0(X6,X5)) = X4) )),
% 2.39/0.70    inference(resolution,[],[f71,f64])).
% 2.39/0.70  fof(f64,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.39/0.70    inference(cnf_transformation,[],[f43])).
% 2.39/0.70  fof(f43,plain,(
% 2.39/0.70    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.39/0.70    inference(nnf_transformation,[],[f6])).
% 2.39/0.70  fof(f6,axiom,(
% 2.39/0.70    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.39/0.70  fof(f71,plain,(
% 2.39/0.70    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f31])).
% 2.39/0.70  fof(f31,plain,(
% 2.39/0.70    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.39/0.70    inference(ennf_transformation,[],[f7])).
% 2.39/0.70  fof(f7,axiom,(
% 2.39/0.70    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 2.39/0.70  fof(f282,plain,(
% 2.39/0.70    ( ! [X2,X3] : (r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.39/0.70    inference(trivial_inequality_removal,[],[f276])).
% 2.39/0.70  fof(f276,plain,(
% 2.39/0.70    ( ! [X2,X3] : (X2 != X2 | r1_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 2.39/0.70    inference(superposition,[],[f65,f200])).
% 2.39/0.70  fof(f65,plain,(
% 2.39/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f43])).
% 2.39/0.70  fof(f362,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,X1),X0) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.39/0.70    inference(resolution,[],[f168,f51])).
% 2.39/0.70  fof(f51,plain,(
% 2.39/0.70    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 2.39/0.70    inference(cnf_transformation,[],[f21])).
% 2.39/0.70  fof(f21,plain,(
% 2.39/0.70    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.39/0.70    inference(ennf_transformation,[],[f4])).
% 2.39/0.70  fof(f4,axiom,(
% 2.39/0.70    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.39/0.70  fof(f168,plain,(
% 2.39/0.70    ( ! [X6,X8,X7] : (r1_xboole_0(X8,k4_xboole_0(X6,X7)) | ~r1_xboole_0(X8,X6)) )),
% 2.39/0.70    inference(superposition,[],[f69,f83])).
% 2.39/0.70  fof(f83,plain,(
% 2.39/0.70    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) )),
% 2.39/0.70    inference(resolution,[],[f59,f58])).
% 2.39/0.70  fof(f58,plain,(
% 2.39/0.70    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f3])).
% 2.39/0.70  fof(f3,axiom,(
% 2.39/0.70    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.39/0.70  fof(f6577,plain,(
% 2.39/0.70    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),sK1) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.39/0.70    inference(superposition,[],[f200,f1727])).
% 2.39/0.70  fof(f1727,plain,(
% 2.39/0.70    sK1 = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.39/0.70    inference(superposition,[],[f463,f608])).
% 2.39/0.70  fof(f608,plain,(
% 2.39/0.70    k1_tops_1(sK0,sK1) = k4_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.39/0.70    inference(resolution,[],[f324,f46])).
% 2.39/0.70  fof(f324,plain,(
% 2.39/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k4_xboole_0(k1_tops_1(sK0,X0),k2_tops_1(sK0,X0))) )),
% 2.39/0.70    inference(resolution,[],[f145,f45])).
% 2.39/0.70  fof(f145,plain,(
% 2.39/0.70    ( ! [X2,X3] : (~l1_pre_topc(X3) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | k1_tops_1(X3,X2) = k4_xboole_0(k1_tops_1(X3,X2),k2_tops_1(X3,X2))) )),
% 2.39/0.70    inference(resolution,[],[f54,f64])).
% 2.39/0.70  fof(f54,plain,(
% 2.39/0.70    ( ! [X0,X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f24])).
% 2.39/0.70  fof(f24,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : (r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f16])).
% 2.39/0.70  fof(f16,axiom,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_1)).
% 2.39/0.70  fof(f463,plain,(
% 2.39/0.70    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k4_xboole_0(X0,k2_tops_1(sK0,sK1))) | k1_xboole_0 = k1_tops_1(sK0,sK1)) )),
% 2.39/0.70    inference(resolution,[],[f206,f243])).
% 2.39/0.70  fof(f243,plain,(
% 2.39/0.70    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 2.39/0.70    inference(resolution,[],[f154,f46])).
% 2.39/0.70  fof(f154,plain,(
% 2.39/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(X0,sK0) | k1_xboole_0 = k1_tops_1(sK0,X0)) )),
% 2.39/0.70    inference(resolution,[],[f56,f45])).
% 2.39/0.70  fof(f56,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f40])).
% 2.39/0.70  fof(f40,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(nnf_transformation,[],[f26])).
% 2.39/0.70  fof(f26,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f17])).
% 2.39/0.70  fof(f17,axiom,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 2.39/0.70  fof(f206,plain,(
% 2.39/0.70    ( ! [X10] : (v2_tops_1(sK1,sK0) | sK1 = k4_xboole_0(sK1,k4_xboole_0(X10,k2_tops_1(sK0,sK1)))) )),
% 2.39/0.70    inference(resolution,[],[f98,f47])).
% 2.39/0.70  fof(f47,plain,(
% 2.39/0.70    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 2.39/0.70    inference(cnf_transformation,[],[f39])).
% 2.39/0.70  fof(f157,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,X1),k1_xboole_0) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.70    inference(subsumption_resolution,[],[f155,f78])).
% 2.39/0.70  fof(f155,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,X1),k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.70    inference(extensionality_resolution,[],[f63,f57])).
% 2.39/0.70  fof(f57,plain,(
% 2.39/0.70    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f40])).
% 2.39/0.70  fof(f63,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f42])).
% 2.39/0.70  fof(f6871,plain,(
% 2.39/0.70    ~v2_tops_1(sK1,sK0)),
% 2.39/0.70    inference(subsumption_resolution,[],[f6849,f180])).
% 2.39/0.70  fof(f180,plain,(
% 2.39/0.70    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.39/0.70    inference(resolution,[],[f131,f46])).
% 2.39/0.70  fof(f131,plain,(
% 2.39/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,k2_pre_topc(sK0,X0))) )),
% 2.39/0.70    inference(resolution,[],[f52,f45])).
% 2.39/0.70  fof(f52,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 2.39/0.70    inference(cnf_transformation,[],[f22])).
% 2.39/0.70  fof(f22,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f13])).
% 2.39/0.70  fof(f13,axiom,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.39/0.70  fof(f6849,plain,(
% 2.39/0.70    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 2.39/0.70    inference(superposition,[],[f48,f6683])).
% 2.39/0.70  fof(f6683,plain,(
% 2.39/0.70    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)),
% 2.39/0.70    inference(forward_demodulation,[],[f6664,f115])).
% 2.39/0.70  fof(f115,plain,(
% 2.39/0.70    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 2.39/0.70    inference(resolution,[],[f100,f64])).
% 2.39/0.70  fof(f100,plain,(
% 2.39/0.70    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.39/0.70    inference(resolution,[],[f97,f75])).
% 2.39/0.70  fof(f97,plain,(
% 2.39/0.70    ( ! [X2,X3] : (~r1_tarski(X2,X3) | r1_xboole_0(X2,k1_xboole_0)) )),
% 2.39/0.70    inference(resolution,[],[f71,f92])).
% 2.39/0.70  fof(f92,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | r1_xboole_0(X1,k1_xboole_0)) )),
% 2.39/0.70    inference(superposition,[],[f69,f84])).
% 2.39/0.70  fof(f84,plain,(
% 2.39/0.70    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) )),
% 2.39/0.70    inference(resolution,[],[f59,f78])).
% 2.39/0.70  fof(f6664,plain,(
% 2.39/0.70    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)),
% 2.39/0.70    inference(superposition,[],[f1525,f6632])).
% 2.39/0.70  fof(f1525,plain,(
% 2.39/0.70    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.39/0.70    inference(superposition,[],[f671,f316])).
% 2.39/0.70  fof(f316,plain,(
% 2.39/0.70    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.39/0.70    inference(resolution,[],[f162,f46])).
% 2.39/0.70  fof(f162,plain,(
% 2.39/0.70    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0))) )),
% 2.39/0.70    inference(resolution,[],[f55,f45])).
% 2.39/0.70  fof(f55,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 2.39/0.70    inference(cnf_transformation,[],[f25])).
% 2.39/0.70  fof(f25,plain,(
% 2.39/0.70    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(ennf_transformation,[],[f14])).
% 2.39/0.70  fof(f14,axiom,(
% 2.39/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.39/0.70  fof(f671,plain,(
% 2.39/0.70    ( ! [X5] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X5) = k4_xboole_0(k2_pre_topc(sK0,sK1),X5)) )),
% 2.39/0.70    inference(resolution,[],[f329,f46])).
% 2.39/0.70  fof(f329,plain,(
% 2.39/0.70    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),X1) = k4_xboole_0(k2_pre_topc(sK0,X0),X1)) )),
% 2.39/0.70    inference(resolution,[],[f146,f45])).
% 2.39/0.70  fof(f146,plain,(
% 2.39/0.70    ( ! [X2,X0,X1] : (~l1_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),X2) = k4_xboole_0(k2_pre_topc(X1,X0),X2)) )),
% 2.39/0.70    inference(resolution,[],[f60,f72])).
% 2.39/0.70  fof(f72,plain,(
% 2.39/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f32])).
% 2.39/0.70  fof(f32,plain,(
% 2.39/0.70    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.39/0.70    inference(ennf_transformation,[],[f8])).
% 2.39/0.70  fof(f8,axiom,(
% 2.39/0.70    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.39/0.70  fof(f60,plain,(
% 2.39/0.70    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.39/0.70    inference(cnf_transformation,[],[f29])).
% 2.39/0.70  fof(f29,plain,(
% 2.39/0.70    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.39/0.70    inference(flattening,[],[f28])).
% 2.39/0.70  fof(f28,plain,(
% 2.39/0.70    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.39/0.70    inference(ennf_transformation,[],[f12])).
% 2.39/0.70  fof(f12,axiom,(
% 2.39/0.70    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.39/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.39/0.70  fof(f48,plain,(
% 2.39/0.70    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 2.39/0.70    inference(cnf_transformation,[],[f39])).
% 2.39/0.70  % SZS output end Proof for theBenchmark
% 2.39/0.70  % (29296)------------------------------
% 2.39/0.70  % (29296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.39/0.70  % (29296)Termination reason: Refutation
% 2.39/0.70  
% 2.39/0.70  % (29296)Memory used [KB]: 5628
% 2.39/0.70  % (29296)Time elapsed: 0.253 s
% 2.39/0.70  % (29296)------------------------------
% 2.39/0.70  % (29296)------------------------------
% 2.39/0.70  % (29279)Success in time 0.339 s
%------------------------------------------------------------------------------
