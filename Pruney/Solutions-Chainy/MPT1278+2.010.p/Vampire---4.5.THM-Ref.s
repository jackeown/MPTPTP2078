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
% DateTime   : Thu Dec  3 13:12:51 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 863 expanded)
%              Number of leaves         :   24 ( 266 expanded)
%              Depth                    :   22
%              Number of atoms          :  378 (4062 expanded)
%              Number of equality atoms :   73 ( 753 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f805,plain,(
    $false ),
    inference(subsumption_resolution,[],[f804,f69])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( k1_xboole_0 != sK1
    & v3_tops_1(sK1,sK0)
    & v3_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK0)
          & v3_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK0)
        & v3_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK1
      & v3_tops_1(sK1,sK0)
      & v3_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f804,plain,(
    k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f794,f653])).

fof(f653,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f625,f625,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f625,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f72,f613,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f613,plain,(
    ! [X1] : ~ r2_hidden(X1,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f610,f113])).

fof(f113,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f610,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k4_xboole_0(sK1,u1_struct_0(sK0))) ) ),
    inference(superposition,[],[f112,f353])).

fof(f353,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f352,f151])).

fof(f151,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f142,f141])).

fof(f141,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f66,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f142,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f66,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f352,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f342,f108])).

fof(f108,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f86,f87,f87])).

fof(f87,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f342,plain,(
    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f153,f89])).

fof(f153,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f140,f141])).

fof(f140,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f66,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f794,plain,(
    ! [X0] : sK1 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f625,f784,f104])).

fof(f784,plain,(
    ! [X1] : ~ r2_hidden(X1,sK1) ),
    inference(subsumption_resolution,[],[f781,f148])).

fof(f148,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f66,f91])).

fof(f781,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f112,f723])).

fof(f723,plain,(
    sK1 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f409,f709])).

fof(f709,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f151,f707])).

fof(f707,plain,(
    u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f706,f464])).

fof(f464,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f335,f462])).

fof(f462,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f461,f400])).

fof(f400,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f128,f311,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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

fof(f311,plain,(
    r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f127,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f127,plain,(
    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f119,f71])).

fof(f71,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f119,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f75,f65,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f128,plain,(
    r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f117,f71])).

fof(f117,plain,(
    r1_tarski(k2_subset_1(u1_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f75,f65,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f461,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f403,f443,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f443,plain,(
    v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f154,f85,f153,f403,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f154,plain,(
    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f138,f141])).

fof(f138,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f65,f68,f66,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f68,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f403,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f127,f400])).

fof(f335,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f154,f153,f82])).

fof(f706,plain,(
    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f65,f153,f702,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f702,plain,(
    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f701,f153])).

fof(f701,plain,
    ( ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f698,f67])).

fof(f67,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f698,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f124,f151])).

fof(f124,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X4),sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X4,sK0) ) ),
    inference(resolution,[],[f65,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f409,plain,(
    k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f309,f400])).

fof(f309,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f127,f89])).
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
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:59 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (10817)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (10826)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (10834)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (10821)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.53  % (10814)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (10808)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (10831)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (10811)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (10823)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (10820)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (10813)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (10812)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (10809)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.55  % (10830)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (10815)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (10810)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (10833)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (10835)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (10822)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (10836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (10836)Refutation not found, incomplete strategy% (10836)------------------------------
% 0.22/0.56  % (10836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (10836)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (10836)Memory used [KB]: 10746
% 0.22/0.56  % (10836)Time elapsed: 0.138 s
% 0.22/0.56  % (10836)------------------------------
% 0.22/0.56  % (10836)------------------------------
% 0.22/0.56  % (10837)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (10827)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (10828)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (10819)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (10829)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.57  % (10818)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.57  % (10818)Refutation not found, incomplete strategy% (10818)------------------------------
% 0.22/0.57  % (10818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (10824)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (10824)Refutation not found, incomplete strategy% (10824)------------------------------
% 0.22/0.57  % (10824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (10824)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (10824)Memory used [KB]: 10746
% 0.22/0.57  % (10824)Time elapsed: 0.156 s
% 0.22/0.57  % (10824)------------------------------
% 0.22/0.57  % (10824)------------------------------
% 1.52/0.57  % (10816)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.52/0.58  % (10832)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.52/0.59  % (10825)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.52/0.59  % (10818)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.59  
% 1.52/0.59  % (10818)Memory used [KB]: 10874
% 1.52/0.59  % (10818)Time elapsed: 0.136 s
% 1.52/0.59  % (10818)------------------------------
% 1.52/0.59  % (10818)------------------------------
% 1.79/0.60  % (10819)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f805,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(subsumption_resolution,[],[f804,f69])).
% 1.79/0.60  fof(f69,plain,(
% 1.79/0.60    k1_xboole_0 != sK1),
% 1.79/0.60    inference(cnf_transformation,[],[f53])).
% 1.79/0.60  fof(f53,plain,(
% 1.79/0.60    (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f52,f51])).
% 1.79/0.60  fof(f51,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    ? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,sK0) & v3_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK1 & v3_tops_1(sK1,sK0) & v3_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f29])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f28])).
% 1.79/0.60  fof(f28,negated_conjecture,(
% 1.79/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.79/0.60    inference(negated_conjecture,[],[f27])).
% 1.79/0.60  fof(f27,conjecture,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 1.79/0.60  fof(f804,plain,(
% 1.79/0.60    k1_xboole_0 = sK1),
% 1.79/0.60    inference(forward_demodulation,[],[f794,f653])).
% 1.79/0.60  fof(f653,plain,(
% 1.79/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f625,f625,f104])).
% 1.79/0.60  fof(f104,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f63])).
% 1.79/0.60  fof(f63,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f61,f62])).
% 1.79/0.60  fof(f62,plain,(
% 1.79/0.60    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.79/0.60    introduced(choice_axiom,[])).
% 1.79/0.60  fof(f61,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(rectify,[],[f60])).
% 1.79/0.60  fof(f60,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(flattening,[],[f59])).
% 1.79/0.60  fof(f59,plain,(
% 1.79/0.60    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.79/0.60    inference(nnf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.79/0.60  fof(f625,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f72,f613,f91])).
% 1.79/0.60  fof(f91,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f43])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f14])).
% 1.79/0.60  fof(f14,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.79/0.60  fof(f613,plain,(
% 1.79/0.60    ( ! [X1] : (~r2_hidden(X1,k4_xboole_0(sK1,u1_struct_0(sK0)))) )),
% 1.79/0.60    inference(subsumption_resolution,[],[f610,f113])).
% 1.79/0.60  fof(f113,plain,(
% 1.79/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f101])).
% 1.79/0.60  fof(f101,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f63])).
% 1.79/0.60  fof(f610,plain,(
% 1.79/0.60    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k4_xboole_0(sK1,u1_struct_0(sK0)))) )),
% 1.79/0.60    inference(superposition,[],[f112,f353])).
% 1.79/0.60  fof(f353,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0)))),
% 1.79/0.60    inference(forward_demodulation,[],[f352,f151])).
% 1.79/0.60  fof(f151,plain,(
% 1.79/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(backward_demodulation,[],[f142,f141])).
% 1.79/0.60  fof(f141,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f66,f89])).
% 1.79/0.60  fof(f89,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f41])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f10])).
% 1.79/0.60  fof(f10,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.79/0.60  fof(f66,plain,(
% 1.79/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(cnf_transformation,[],[f53])).
% 1.79/0.60  fof(f142,plain,(
% 1.79/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f66,f90])).
% 1.79/0.60  fof(f90,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f42])).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.79/0.60  fof(f352,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK1,u1_struct_0(sK0)))),
% 1.79/0.60    inference(forward_demodulation,[],[f342,f108])).
% 1.79/0.60  fof(f108,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f86,f87,f87])).
% 1.79/0.60  fof(f87,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.79/0.60  fof(f86,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.79/0.60  fof(f342,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f153,f89])).
% 1.79/0.60  fof(f153,plain,(
% 1.79/0.60    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(forward_demodulation,[],[f140,f141])).
% 1.79/0.60  fof(f140,plain,(
% 1.79/0.60    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f66,f88])).
% 1.79/0.60  fof(f88,plain,(
% 1.79/0.60    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f40])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.79/0.60  fof(f112,plain,(
% 1.79/0.60    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.79/0.60    inference(equality_resolution,[],[f102])).
% 1.79/0.60  fof(f102,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f63])).
% 1.79/0.60  fof(f72,plain,(
% 1.79/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,axiom,(
% 1.79/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.79/0.60  fof(f794,plain,(
% 1.79/0.60    ( ! [X0] : (sK1 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f625,f784,f104])).
% 1.79/0.60  fof(f784,plain,(
% 1.79/0.60    ( ! [X1] : (~r2_hidden(X1,sK1)) )),
% 1.79/0.60    inference(subsumption_resolution,[],[f781,f148])).
% 1.79/0.60  fof(f148,plain,(
% 1.79/0.60    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1)) )),
% 1.79/0.60    inference(resolution,[],[f66,f91])).
% 1.79/0.60  fof(f781,plain,(
% 1.79/0.60    ( ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,u1_struct_0(sK0))) )),
% 1.79/0.60    inference(superposition,[],[f112,f723])).
% 1.79/0.60  fof(f723,plain,(
% 1.79/0.60    sK1 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.79/0.60    inference(backward_demodulation,[],[f409,f709])).
% 1.79/0.60  fof(f709,plain,(
% 1.79/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.79/0.60    inference(backward_demodulation,[],[f151,f707])).
% 1.79/0.60  fof(f707,plain,(
% 1.79/0.60    u1_struct_0(sK0) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.79/0.60    inference(forward_demodulation,[],[f706,f464])).
% 1.79/0.60  fof(f464,plain,(
% 1.79/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(backward_demodulation,[],[f335,f462])).
% 1.79/0.60  fof(f462,plain,(
% 1.79/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.79/0.60    inference(forward_demodulation,[],[f461,f400])).
% 1.79/0.60  fof(f400,plain,(
% 1.79/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f128,f311,f96])).
% 1.79/0.60  fof(f96,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f57])).
% 1.79/0.60  fof(f57,plain,(
% 1.79/0.60    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.60    inference(flattening,[],[f56])).
% 1.79/0.60  fof(f56,plain,(
% 1.79/0.60    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.79/0.60    inference(nnf_transformation,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.79/0.60  fof(f311,plain,(
% 1.79/0.60    r1_tarski(k2_pre_topc(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f127,f97])).
% 1.79/0.60  fof(f97,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f58])).
% 1.79/0.60  fof(f58,plain,(
% 1.79/0.60    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.79/0.60    inference(nnf_transformation,[],[f17])).
% 1.79/0.60  fof(f17,axiom,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.79/0.60  fof(f127,plain,(
% 1.79/0.60    m1_subset_1(k2_pre_topc(sK0,u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(forward_demodulation,[],[f119,f71])).
% 1.79/0.60  fof(f71,plain,(
% 1.79/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.79/0.60    inference(cnf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.79/0.60  fof(f119,plain,(
% 1.79/0.60    m1_subset_1(k2_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f75,f65,f93])).
% 1.79/0.60  fof(f93,plain,(
% 1.79/0.60    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f47])).
% 1.79/0.60  fof(f47,plain,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f46])).
% 1.79/0.60  fof(f46,plain,(
% 1.79/0.60    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,axiom,(
% 1.79/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.79/0.60  fof(f65,plain,(
% 1.79/0.60    l1_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f53])).
% 1.79/0.60  fof(f75,plain,(
% 1.79/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f11])).
% 1.79/0.60  fof(f11,axiom,(
% 1.79/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.79/0.60  fof(f128,plain,(
% 1.79/0.60    r1_tarski(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))),
% 1.79/0.60    inference(forward_demodulation,[],[f117,f71])).
% 1.79/0.60  fof(f117,plain,(
% 1.79/0.60    r1_tarski(k2_subset_1(u1_struct_0(sK0)),k2_pre_topc(sK0,k2_subset_1(u1_struct_0(sK0))))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f75,f65,f76])).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f21])).
% 1.79/0.60  fof(f21,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.79/0.60  fof(f461,plain,(
% 1.79/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f65,f403,f443,f82])).
% 1.79/0.60  fof(f82,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(nnf_transformation,[],[f37])).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f23])).
% 1.79/0.60  fof(f23,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.79/0.60  fof(f443,plain,(
% 1.79/0.60    v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f65,f154,f85,f153,f403,f84])).
% 1.79/0.60  fof(f84,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X2,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f39])).
% 1.79/0.60  fof(f39,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f38])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f25])).
% 1.79/0.60  fof(f25,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_1)).
% 1.79/0.60  fof(f85,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.79/0.60  fof(f154,plain,(
% 1.79/0.60    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(forward_demodulation,[],[f138,f141])).
% 1.79/0.60  fof(f138,plain,(
% 1.79/0.60    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f65,f68,f66,f79])).
% 1.79/0.60  fof(f79,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f35])).
% 1.79/0.60  fof(f35,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f34])).
% 1.79/0.60  fof(f34,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f26])).
% 1.79/0.60  fof(f26,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 1.79/0.60  fof(f68,plain,(
% 1.79/0.60    v3_tops_1(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f53])).
% 1.79/0.60  fof(f403,plain,(
% 1.79/0.60    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(backward_demodulation,[],[f127,f400])).
% 1.79/0.60  fof(f335,plain,(
% 1.79/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f65,f154,f153,f82])).
% 1.79/0.60  fof(f706,plain,(
% 1.79/0.60    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f65,f153,f702,f77])).
% 1.79/0.60  fof(f77,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f22])).
% 1.79/0.60  fof(f22,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.79/0.60  fof(f702,plain,(
% 1.79/0.60    v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(subsumption_resolution,[],[f701,f153])).
% 1.79/0.60  fof(f701,plain,(
% 1.79/0.60    ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(subsumption_resolution,[],[f698,f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    v3_pre_topc(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f53])).
% 1.79/0.60  fof(f698,plain,(
% 1.79/0.60    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.79/0.60    inference(superposition,[],[f124,f151])).
% 1.79/0.60  fof(f124,plain,(
% 1.79/0.60    ( ! [X4] : (~v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X4),sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X4,sK0)) )),
% 1.79/0.60    inference(resolution,[],[f65,f81])).
% 1.79/0.60  fof(f81,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f54])).
% 1.79/0.60  fof(f54,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(nnf_transformation,[],[f36])).
% 1.79/0.60  fof(f36,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f24])).
% 1.79/0.60  fof(f24,axiom,(
% 1.79/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 1.79/0.60  fof(f409,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))),
% 1.79/0.60    inference(backward_demodulation,[],[f309,f400])).
% 1.79/0.60  fof(f309,plain,(
% 1.79/0.60    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) = k4_xboole_0(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f127,f89])).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (10819)------------------------------
% 1.79/0.60  % (10819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (10819)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (10819)Memory used [KB]: 6652
% 1.79/0.60  % (10819)Time elapsed: 0.185 s
% 1.79/0.60  % (10819)------------------------------
% 1.79/0.60  % (10819)------------------------------
% 1.79/0.61  % (10807)Success in time 0.235 s
%------------------------------------------------------------------------------
