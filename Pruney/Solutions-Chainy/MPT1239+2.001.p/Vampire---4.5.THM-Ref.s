%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:10 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 228 expanded)
%              Number of leaves         :   13 (  55 expanded)
%              Depth                    :   19
%              Number of atoms          :  169 ( 568 expanded)
%              Number of equality atoms :   20 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4498,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4497,f187])).

fof(f187,plain,(
    ! [X14] : r1_tarski(k4_xboole_0(sK1,X14),u1_struct_0(sK0)) ),
    inference(superposition,[],[f143,f69])).

fof(f69,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f143,plain,(
    ! [X12,X13,X11] : r1_tarski(k4_xboole_0(X11,X12),k2_xboole_0(X11,X13)) ),
    inference(superposition,[],[f96,f68])).

fof(f68,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f96,plain,(
    ! [X4,X2,X3] : r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4)) ),
    inference(resolution,[],[f53,f39])).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f4497,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f4496,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4496,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f4495,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f4495,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f4494,f40])).

fof(f4494,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f4493,f34])).

fof(f4493,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f4492,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f4492,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3761,f4490])).

fof(f4490,plain,(
    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(superposition,[],[f2721,f2759])).

fof(f2759,plain,(
    ! [X44] : k4_xboole_0(X44,k1_tops_1(sK0,k4_xboole_0(sK1,X44))) = X44 ),
    inference(resolution,[],[f2742,f2697])).

fof(f2697,plain,(
    ! [X0] : r1_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X0))) ),
    inference(resolution,[],[f2692,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2692,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0) ),
    inference(resolution,[],[f2437,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f2437,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f2110,f187])).

fof(f2110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f760,f48])).

fof(f760,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f37,f36])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2742,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f2738,f56])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2738,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f512,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f512,plain,(
    ! [X17,X18] :
      ( ~ r1_tarski(X17,k4_xboole_0(X17,X18))
      | k4_xboole_0(X17,X18) = X17 ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2721,plain,(
    ! [X0] : r1_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK2,X0))) ),
    inference(resolution,[],[f2716,f43])).

fof(f2716,plain,(
    ! [X0] : r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK2,X0)),X0) ),
    inference(resolution,[],[f2438,f52])).

fof(f2438,plain,(
    ! [X1] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK2,X1)),k4_xboole_0(sK2,X1)) ),
    inference(resolution,[],[f2110,f188])).

fof(f188,plain,(
    ! [X15] : r1_tarski(k4_xboole_0(sK2,X15),u1_struct_0(sK0)) ),
    inference(superposition,[],[f143,f70])).

fof(f70,plain,(
    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f49,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f3761,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f3361,f55])).

fof(f3361,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f1260,f3340])).

fof(f3340,plain,(
    ! [X231] : k4_xboole_0(k1_tops_1(sK0,sK1),X231) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X231) ),
    inference(resolution,[],[f1259,f2373])).

fof(f2373,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f2183,f69])).

fof(f2183,plain,(
    ! [X1] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f96,f2116])).

fof(f2116,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f2109,f44])).

fof(f2109,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f760,f34])).

fof(f1259,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1260,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f33,f1258])).

fof(f1258,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f50,f34])).

fof(f33,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:04:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (22297)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (22302)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.50  % (22304)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (22285)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (22283)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (22284)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (22286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (22289)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (22306)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (22294)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (22293)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (22301)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (22290)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (22303)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (22298)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (22296)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (22287)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (22295)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (22305)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (22288)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (22291)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (22308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (22307)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (22300)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (22299)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (22292)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 2.11/0.71  % (22292)Refutation not found, incomplete strategy% (22292)------------------------------
% 2.11/0.71  % (22292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.71  % (22292)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.71  
% 2.11/0.71  % (22292)Memory used [KB]: 6140
% 2.11/0.71  % (22292)Time elapsed: 0.297 s
% 2.11/0.71  % (22292)------------------------------
% 2.11/0.71  % (22292)------------------------------
% 2.86/0.79  % (22302)Refutation found. Thanks to Tanya!
% 2.86/0.79  % SZS status Theorem for theBenchmark
% 2.86/0.79  % SZS output start Proof for theBenchmark
% 2.86/0.79  fof(f4498,plain,(
% 2.86/0.79    $false),
% 2.86/0.79    inference(subsumption_resolution,[],[f4497,f187])).
% 2.86/0.79  fof(f187,plain,(
% 2.86/0.79    ( ! [X14] : (r1_tarski(k4_xboole_0(sK1,X14),u1_struct_0(sK0))) )),
% 2.86/0.79    inference(superposition,[],[f143,f69])).
% 2.86/0.79  fof(f69,plain,(
% 2.86/0.79    u1_struct_0(sK0) = k2_xboole_0(sK1,u1_struct_0(sK0))),
% 2.86/0.79    inference(resolution,[],[f44,f63])).
% 2.86/0.79  fof(f63,plain,(
% 2.86/0.79    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.86/0.79    inference(resolution,[],[f49,f34])).
% 2.86/0.79  fof(f34,plain,(
% 2.86/0.79    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.86/0.79    inference(cnf_transformation,[],[f19])).
% 2.86/0.79  fof(f19,plain,(
% 2.86/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.86/0.79    inference(flattening,[],[f18])).
% 2.86/0.79  fof(f18,plain,(
% 2.86/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.86/0.79    inference(ennf_transformation,[],[f17])).
% 2.86/0.79  fof(f17,negated_conjecture,(
% 2.86/0.79    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.86/0.79    inference(negated_conjecture,[],[f16])).
% 2.86/0.79  fof(f16,conjecture,(
% 2.86/0.79    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 2.86/0.79  fof(f49,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f13])).
% 2.86/0.79  fof(f13,axiom,(
% 2.86/0.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.86/0.79  fof(f44,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.86/0.79    inference(cnf_transformation,[],[f24])).
% 2.86/0.79  fof(f24,plain,(
% 2.86/0.79    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.86/0.79    inference(ennf_transformation,[],[f6])).
% 2.86/0.79  fof(f6,axiom,(
% 2.86/0.79    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.86/0.79  fof(f143,plain,(
% 2.86/0.79    ( ! [X12,X13,X11] : (r1_tarski(k4_xboole_0(X11,X12),k2_xboole_0(X11,X13))) )),
% 2.86/0.79    inference(superposition,[],[f96,f68])).
% 2.86/0.79  fof(f68,plain,(
% 2.86/0.79    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 2.86/0.79    inference(resolution,[],[f44,f40])).
% 2.86/0.79  fof(f40,plain,(
% 2.86/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f7])).
% 2.86/0.79  fof(f7,axiom,(
% 2.86/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.86/0.79  fof(f96,plain,(
% 2.86/0.79    ( ! [X4,X2,X3] : (r1_tarski(X2,k2_xboole_0(k2_xboole_0(X2,X3),X4))) )),
% 2.86/0.79    inference(resolution,[],[f53,f39])).
% 2.86/0.79  fof(f39,plain,(
% 2.86/0.79    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.86/0.79    inference(cnf_transformation,[],[f10])).
% 2.86/0.79  fof(f10,axiom,(
% 2.86/0.79    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.86/0.79  fof(f53,plain,(
% 2.86/0.79    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f27])).
% 2.86/0.79  fof(f27,plain,(
% 2.86/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.86/0.79    inference(ennf_transformation,[],[f5])).
% 2.86/0.79  fof(f5,axiom,(
% 2.86/0.79    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 2.86/0.79  fof(f4497,plain,(
% 2.86/0.79    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 2.86/0.79    inference(resolution,[],[f4496,f48])).
% 2.86/0.79  fof(f48,plain,(
% 2.86/0.79    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f13])).
% 2.86/0.79  fof(f4496,plain,(
% 2.86/0.79    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.86/0.79    inference(subsumption_resolution,[],[f4495,f36])).
% 2.86/0.79  fof(f36,plain,(
% 2.86/0.79    l1_pre_topc(sK0)),
% 2.86/0.79    inference(cnf_transformation,[],[f19])).
% 2.86/0.79  fof(f4495,plain,(
% 2.86/0.79    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.86/0.79    inference(subsumption_resolution,[],[f4494,f40])).
% 2.86/0.79  fof(f4494,plain,(
% 2.86/0.79    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 2.86/0.79    inference(subsumption_resolution,[],[f4493,f34])).
% 2.86/0.79  fof(f4493,plain,(
% 2.86/0.79    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 2.86/0.79    inference(resolution,[],[f4492,f38])).
% 2.86/0.79  fof(f38,plain,(
% 2.86/0.79    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f22])).
% 2.86/0.79  fof(f22,plain,(
% 2.86/0.79    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.86/0.79    inference(flattening,[],[f21])).
% 2.86/0.79  fof(f21,plain,(
% 2.86/0.79    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.86/0.79    inference(ennf_transformation,[],[f15])).
% 2.86/0.79  fof(f15,axiom,(
% 2.86/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 2.86/0.79  fof(f4492,plain,(
% 2.86/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.86/0.79    inference(subsumption_resolution,[],[f3761,f4490])).
% 2.86/0.79  fof(f4490,plain,(
% 2.86/0.79    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 2.86/0.79    inference(superposition,[],[f2721,f2759])).
% 2.86/0.79  fof(f2759,plain,(
% 2.86/0.79    ( ! [X44] : (k4_xboole_0(X44,k1_tops_1(sK0,k4_xboole_0(sK1,X44))) = X44) )),
% 2.86/0.79    inference(resolution,[],[f2742,f2697])).
% 2.86/0.79  fof(f2697,plain,(
% 2.86/0.79    ( ! [X0] : (r1_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK1,X0)))) )),
% 2.86/0.79    inference(resolution,[],[f2692,f43])).
% 2.86/0.79  fof(f43,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f23])).
% 2.86/0.79  fof(f23,plain,(
% 2.86/0.79    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.86/0.79    inference(ennf_transformation,[],[f2])).
% 2.86/0.79  fof(f2,axiom,(
% 2.86/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.86/0.79  fof(f2692,plain,(
% 2.86/0.79    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),X0)) )),
% 2.86/0.79    inference(resolution,[],[f2437,f52])).
% 2.86/0.79  fof(f52,plain,(
% 2.86/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f26])).
% 2.86/0.79  fof(f26,plain,(
% 2.86/0.79    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.86/0.79    inference(ennf_transformation,[],[f4])).
% 2.86/0.79  fof(f4,axiom,(
% 2.86/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.86/0.79  fof(f2437,plain,(
% 2.86/0.79    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0))) )),
% 2.86/0.79    inference(resolution,[],[f2110,f187])).
% 2.86/0.79  fof(f2110,plain,(
% 2.86/0.79    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.86/0.79    inference(resolution,[],[f760,f48])).
% 2.86/0.79  fof(f760,plain,(
% 2.86/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.86/0.79    inference(resolution,[],[f37,f36])).
% 2.86/0.79  fof(f37,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f20])).
% 2.86/0.79  fof(f20,plain,(
% 2.86/0.79    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.86/0.79    inference(ennf_transformation,[],[f14])).
% 2.86/0.79  fof(f14,axiom,(
% 2.86/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 2.86/0.79  fof(f2742,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.86/0.79    inference(subsumption_resolution,[],[f2738,f56])).
% 2.86/0.79  fof(f56,plain,(
% 2.86/0.79    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.86/0.79    inference(equality_resolution,[],[f46])).
% 2.86/0.79  fof(f46,plain,(
% 2.86/0.79    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.86/0.79    inference(cnf_transformation,[],[f3])).
% 2.86/0.79  fof(f3,axiom,(
% 2.86/0.79    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.86/0.79  fof(f2738,plain,(
% 2.86/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X0)) )),
% 2.86/0.79    inference(resolution,[],[f512,f55])).
% 2.86/0.79  fof(f55,plain,(
% 2.86/0.79    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f31])).
% 2.86/0.79  fof(f31,plain,(
% 2.86/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.86/0.79    inference(flattening,[],[f30])).
% 2.86/0.79  fof(f30,plain,(
% 2.86/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.86/0.79    inference(ennf_transformation,[],[f11])).
% 2.86/0.79  fof(f11,axiom,(
% 2.86/0.79    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.86/0.79  fof(f512,plain,(
% 2.86/0.79    ( ! [X17,X18] : (~r1_tarski(X17,k4_xboole_0(X17,X18)) | k4_xboole_0(X17,X18) = X17) )),
% 2.86/0.79    inference(resolution,[],[f47,f40])).
% 2.86/0.79  fof(f47,plain,(
% 2.86/0.79    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.86/0.79    inference(cnf_transformation,[],[f3])).
% 2.86/0.79  fof(f2721,plain,(
% 2.86/0.79    ( ! [X0] : (r1_xboole_0(X0,k1_tops_1(sK0,k4_xboole_0(sK2,X0)))) )),
% 2.86/0.79    inference(resolution,[],[f2716,f43])).
% 2.86/0.79  fof(f2716,plain,(
% 2.86/0.79    ( ! [X0] : (r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK2,X0)),X0)) )),
% 2.86/0.79    inference(resolution,[],[f2438,f52])).
% 2.86/0.79  fof(f2438,plain,(
% 2.86/0.79    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK2,X1)),k4_xboole_0(sK2,X1))) )),
% 2.86/0.79    inference(resolution,[],[f2110,f188])).
% 2.86/0.79  fof(f188,plain,(
% 2.86/0.79    ( ! [X15] : (r1_tarski(k4_xboole_0(sK2,X15),u1_struct_0(sK0))) )),
% 2.86/0.79    inference(superposition,[],[f143,f70])).
% 2.86/0.79  fof(f70,plain,(
% 2.86/0.79    u1_struct_0(sK0) = k2_xboole_0(sK2,u1_struct_0(sK0))),
% 2.86/0.79    inference(resolution,[],[f44,f62])).
% 2.86/0.79  fof(f62,plain,(
% 2.86/0.79    r1_tarski(sK2,u1_struct_0(sK0))),
% 2.86/0.79    inference(resolution,[],[f49,f32])).
% 2.86/0.79  fof(f32,plain,(
% 2.86/0.79    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.86/0.79    inference(cnf_transformation,[],[f19])).
% 2.86/0.79  fof(f3761,plain,(
% 2.86/0.79    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.86/0.79    inference(resolution,[],[f3361,f55])).
% 2.86/0.79  fof(f3361,plain,(
% 2.86/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.86/0.79    inference(backward_demodulation,[],[f1260,f3340])).
% 2.86/0.79  fof(f3340,plain,(
% 2.86/0.79    ( ! [X231] : (k4_xboole_0(k1_tops_1(sK0,sK1),X231) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X231)) )),
% 2.86/0.79    inference(resolution,[],[f1259,f2373])).
% 2.86/0.79  fof(f2373,plain,(
% 2.86/0.79    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.86/0.79    inference(superposition,[],[f2183,f69])).
% 2.86/0.79  fof(f2183,plain,(
% 2.86/0.79    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(sK1,X1))) )),
% 2.86/0.79    inference(superposition,[],[f96,f2116])).
% 2.86/0.79  fof(f2116,plain,(
% 2.86/0.79    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.86/0.79    inference(resolution,[],[f2109,f44])).
% 2.86/0.79  fof(f2109,plain,(
% 2.86/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.86/0.79    inference(resolution,[],[f760,f34])).
% 2.86/0.79  fof(f1259,plain,(
% 2.86/0.79    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 2.86/0.79    inference(resolution,[],[f50,f48])).
% 2.86/0.79  fof(f50,plain,(
% 2.86/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.86/0.79    inference(cnf_transformation,[],[f25])).
% 2.86/0.79  fof(f25,plain,(
% 2.86/0.79    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.86/0.79    inference(ennf_transformation,[],[f12])).
% 2.86/0.79  fof(f12,axiom,(
% 2.86/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.86/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.86/0.79  fof(f1260,plain,(
% 2.86/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.86/0.79    inference(backward_demodulation,[],[f33,f1258])).
% 2.86/0.79  fof(f1258,plain,(
% 2.86/0.79    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 2.86/0.79    inference(resolution,[],[f50,f34])).
% 2.86/0.79  fof(f33,plain,(
% 2.86/0.79    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.86/0.79    inference(cnf_transformation,[],[f19])).
% 2.86/0.79  % SZS output end Proof for theBenchmark
% 2.86/0.79  % (22302)------------------------------
% 2.86/0.79  % (22302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.79  % (22302)Termination reason: Refutation
% 2.86/0.79  
% 2.86/0.79  % (22302)Memory used [KB]: 4605
% 2.86/0.79  % (22302)Time elapsed: 0.352 s
% 2.86/0.79  % (22302)------------------------------
% 2.86/0.79  % (22302)------------------------------
% 2.86/0.79  % (22282)Success in time 0.435 s
%------------------------------------------------------------------------------
