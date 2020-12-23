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
% DateTime   : Thu Dec  3 13:12:08 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 470 expanded)
%              Number of leaves         :   23 ( 131 expanded)
%              Depth                    :   25
%              Number of atoms          :  315 (2032 expanded)
%              Number of equality atoms :  112 ( 631 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2208,plain,(
    $false ),
    inference(resolution,[],[f2207,f57])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
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
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).

fof(f2207,plain,(
    ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f2205,f56])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f2205,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f2204,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

fof(f2204,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(trivial_inequality_removal,[],[f2202])).

fof(f2202,plain,
    ( sK1 != sK1
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(backward_demodulation,[],[f1909,f1694])).

fof(f1694,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f1677,f299])).

fof(f299,plain,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f166,f259])).

fof(f259,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f122,f139])).

fof(f139,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f127,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f94,f75])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f94,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f78,f80])).

fof(f80,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f89,f84])).

fof(f84,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f83,f74,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f122,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(resolution,[],[f72,f93])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f86,f87])).

fof(f87,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f166,plain,(
    ! [X0] : k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f164,f93])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0 ) ),
    inference(forward_demodulation,[],[f82,f87])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1677,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(resolution,[],[f422,f80])).

fof(f422,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | k2_xboole_0(X1,X2) = k4_subset_1(X1,X1,X2) ) ),
    inference(resolution,[],[f199,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X0,X1) = k4_subset_1(X0,X0,X1) ) ),
    inference(resolution,[],[f81,f93])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1909,plain,
    ( sK1 != k2_xboole_0(sK1,k1_xboole_0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(backward_demodulation,[],[f905,f1901])).

fof(f1901,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1248,f1871])).

fof(f1871,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f85,f1804])).

fof(f1804,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1774,f139])).

fof(f1774,plain,(
    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f463,f897])).

fof(f897,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1)) ),
    inference(superposition,[],[f110,f885])).

fof(f885,plain,(
    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f880,f57])).

fof(f880,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f877])).

fof(f877,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f876,f161])).

fof(f161,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f59,f159])).

fof(f159,plain,(
    ! [X9] : k7_subset_1(u1_struct_0(sK0),sK1,X9) = k4_xboole_0(sK1,X9) ),
    inference(resolution,[],[f61,f58])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f59,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f876,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f871,f235])).

fof(f235,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f234,f57])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f231,f159])).

fof(f231,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f62,f58])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f871,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f184,f58])).

fof(f184,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X0,X1)
      | k2_tops_1(X1,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k2_tops_1(X1,X0)))
      | ~ l1_pre_topc(X1) ) ),
    inference(forward_demodulation,[],[f180,f89])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_tops_1(X1,X0) = k4_xboole_0(k2_tops_1(X1,X0),k4_xboole_0(k2_tops_1(X1,X0),X0)) ) ),
    inference(resolution,[],[f64,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f79,f74])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f110,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2)) ),
    inference(resolution,[],[f88,f75])).

fof(f463,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f110,f89])).

fof(f85,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1248,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1247,f57])).

fof(f1247,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1242,f249])).

fof(f249,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f241,f57])).

fof(f241,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f65,f58])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f1242,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f255,f58])).

fof(f255,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f204,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f204,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | k4_subset_1(u1_struct_0(sK0),sK1,X12) = k2_xboole_0(sK1,X12) ) ),
    inference(resolution,[],[f81,f58])).

fof(f905,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f901,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f901,plain,(
    ~ v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f886])).

fof(f886,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f160,f885])).

fof(f160,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f60,f159])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:46:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (1429)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.49  % (1421)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.49  % (1412)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (1410)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.51  % (1408)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.51  % (1409)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.52  % (1415)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.22/0.52  % (1419)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.52  % (1433)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.52  % (1430)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % (1411)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.53  % (1406)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  % (1435)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.53  % (1417)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.53  % (1416)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.54  % (1436)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (1422)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.54  % (1416)Refutation not found, incomplete strategy% (1416)------------------------------
% 1.34/0.54  % (1416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (1416)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (1416)Memory used [KB]: 10746
% 1.34/0.54  % (1416)Time elapsed: 0.139 s
% 1.34/0.54  % (1416)------------------------------
% 1.34/0.54  % (1416)------------------------------
% 1.34/0.54  % (1434)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (1422)Refutation not found, incomplete strategy% (1422)------------------------------
% 1.34/0.54  % (1422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (1422)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (1422)Memory used [KB]: 10746
% 1.34/0.54  % (1422)Time elapsed: 0.139 s
% 1.34/0.54  % (1422)------------------------------
% 1.34/0.54  % (1422)------------------------------
% 1.34/0.54  % (1435)Refutation not found, incomplete strategy% (1435)------------------------------
% 1.34/0.54  % (1435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (1432)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (1407)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (1435)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (1435)Memory used [KB]: 10746
% 1.34/0.54  % (1435)Time elapsed: 0.128 s
% 1.34/0.54  % (1435)------------------------------
% 1.34/0.54  % (1435)------------------------------
% 1.34/0.54  % (1426)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.34/0.54  % (1413)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.54  % (1428)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (1427)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (1425)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (1418)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.55  % (1420)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.55  % (1414)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (1431)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.56  % (1423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.06/0.64  % (1411)Refutation found. Thanks to Tanya!
% 2.06/0.64  % SZS status Theorem for theBenchmark
% 2.06/0.66  % (1489)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.06/0.66  % SZS output start Proof for theBenchmark
% 2.06/0.66  fof(f2208,plain,(
% 2.06/0.66    $false),
% 2.06/0.66    inference(resolution,[],[f2207,f57])).
% 2.06/0.66  fof(f57,plain,(
% 2.06/0.66    l1_pre_topc(sK0)),
% 2.06/0.66    inference(cnf_transformation,[],[f52])).
% 2.06/0.66  fof(f52,plain,(
% 2.06/0.66    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.06/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f51,f50])).
% 2.06/0.66  fof(f50,plain,(
% 2.06/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.06/0.66    introduced(choice_axiom,[])).
% 2.06/0.66  fof(f51,plain,(
% 2.06/0.66    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.06/0.66    introduced(choice_axiom,[])).
% 2.06/0.66  fof(f49,plain,(
% 2.06/0.66    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.66    inference(flattening,[],[f48])).
% 2.06/0.66  fof(f48,plain,(
% 2.06/0.66    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.66    inference(nnf_transformation,[],[f30])).
% 2.06/0.66  fof(f30,plain,(
% 2.06/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.06/0.66    inference(flattening,[],[f29])).
% 2.06/0.66  fof(f29,plain,(
% 2.06/0.66    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f28])).
% 2.06/0.66  fof(f28,negated_conjecture,(
% 2.06/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.06/0.66    inference(negated_conjecture,[],[f27])).
% 2.06/0.66  fof(f27,conjecture,(
% 2.06/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tops_1)).
% 2.06/0.66  fof(f2207,plain,(
% 2.06/0.66    ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f2205,f56])).
% 2.06/0.66  fof(f56,plain,(
% 2.06/0.66    v2_pre_topc(sK0)),
% 2.06/0.66    inference(cnf_transformation,[],[f52])).
% 2.06/0.66  fof(f2205,plain,(
% 2.06/0.66    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f2204,f58])).
% 2.06/0.66  fof(f58,plain,(
% 2.06/0.66    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.06/0.66    inference(cnf_transformation,[],[f52])).
% 2.06/0.66  fof(f2204,plain,(
% 2.06/0.66    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(trivial_inequality_removal,[],[f2202])).
% 2.06/0.66  fof(f2202,plain,(
% 2.06/0.66    sK1 != sK1 | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(backward_demodulation,[],[f1909,f1694])).
% 2.06/0.66  fof(f1694,plain,(
% 2.06/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.66    inference(forward_demodulation,[],[f1677,f299])).
% 2.06/0.66  fof(f299,plain,(
% 2.06/0.66    ( ! [X0] : (k4_subset_1(X0,X0,k1_xboole_0) = X0) )),
% 2.06/0.66    inference(forward_demodulation,[],[f166,f259])).
% 2.06/0.66  fof(f259,plain,(
% 2.06/0.66    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 2.06/0.66    inference(forward_demodulation,[],[f122,f139])).
% 2.06/0.66  fof(f139,plain,(
% 2.06/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.06/0.66    inference(forward_demodulation,[],[f127,f105])).
% 2.06/0.66  fof(f105,plain,(
% 2.06/0.66    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.06/0.66    inference(resolution,[],[f94,f75])).
% 2.06/0.66  fof(f75,plain,(
% 2.06/0.66    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f7])).
% 2.06/0.66  fof(f7,axiom,(
% 2.06/0.66    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.06/0.66  fof(f94,plain,(
% 2.06/0.66    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.06/0.66    inference(resolution,[],[f78,f80])).
% 2.06/0.66  fof(f80,plain,(
% 2.06/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f6])).
% 2.06/0.66  fof(f6,axiom,(
% 2.06/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.06/0.66  fof(f78,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.06/0.66    inference(cnf_transformation,[],[f55])).
% 2.06/0.66  fof(f55,plain,(
% 2.06/0.66    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.66    inference(flattening,[],[f54])).
% 2.06/0.66  fof(f54,plain,(
% 2.06/0.66    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.66    inference(nnf_transformation,[],[f3])).
% 2.06/0.66  fof(f3,axiom,(
% 2.06/0.66    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.66  fof(f127,plain,(
% 2.06/0.66    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 2.06/0.66    inference(superposition,[],[f89,f84])).
% 2.06/0.66  fof(f84,plain,(
% 2.06/0.66    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.06/0.66    inference(cnf_transformation,[],[f9])).
% 2.06/0.66  fof(f9,axiom,(
% 2.06/0.66    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.06/0.66  fof(f89,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.06/0.66    inference(definition_unfolding,[],[f83,f74,f74])).
% 2.06/0.66  fof(f74,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f10])).
% 2.06/0.66  fof(f10,axiom,(
% 2.06/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.06/0.66  fof(f83,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f1])).
% 2.06/0.66  fof(f1,axiom,(
% 2.06/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.06/0.66  fof(f122,plain,(
% 2.06/0.66    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 2.06/0.66    inference(resolution,[],[f72,f93])).
% 2.06/0.66  fof(f93,plain,(
% 2.06/0.66    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.06/0.66    inference(forward_demodulation,[],[f86,f87])).
% 2.06/0.66  fof(f87,plain,(
% 2.06/0.66    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.06/0.66    inference(cnf_transformation,[],[f11])).
% 2.06/0.66  fof(f11,axiom,(
% 2.06/0.66    ! [X0] : k2_subset_1(X0) = X0),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 2.06/0.66  fof(f86,plain,(
% 2.06/0.66    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f13])).
% 2.06/0.66  fof(f13,axiom,(
% 2.06/0.66    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.06/0.66  fof(f72,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f42])).
% 2.06/0.66  fof(f42,plain,(
% 2.06/0.66    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f12])).
% 2.06/0.66  fof(f12,axiom,(
% 2.06/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.06/0.66  fof(f166,plain,(
% 2.06/0.66    ( ! [X0] : (k4_subset_1(X0,X0,k3_subset_1(X0,X0)) = X0) )),
% 2.06/0.66    inference(resolution,[],[f164,f93])).
% 2.06/0.66  fof(f164,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0) )),
% 2.06/0.66    inference(forward_demodulation,[],[f82,f87])).
% 2.06/0.66  fof(f82,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.66    inference(cnf_transformation,[],[f47])).
% 2.06/0.66  fof(f47,plain,(
% 2.06/0.66    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f18])).
% 2.06/0.66  fof(f18,axiom,(
% 2.06/0.66    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 2.06/0.66  fof(f1677,plain,(
% 2.06/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0)) )),
% 2.06/0.66    inference(resolution,[],[f422,f80])).
% 2.06/0.66  fof(f422,plain,(
% 2.06/0.66    ( ! [X2,X1] : (~r1_tarski(X2,X1) | k2_xboole_0(X1,X2) = k4_subset_1(X1,X1,X2)) )),
% 2.06/0.66    inference(resolution,[],[f199,f70])).
% 2.06/0.66  fof(f70,plain,(
% 2.06/0.66    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f53])).
% 2.06/0.66  fof(f53,plain,(
% 2.06/0.66    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.06/0.66    inference(nnf_transformation,[],[f20])).
% 2.06/0.66  fof(f20,axiom,(
% 2.06/0.66    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.06/0.66  fof(f199,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X0,X1) = k4_subset_1(X0,X0,X1)) )),
% 2.06/0.66    inference(resolution,[],[f81,f93])).
% 2.06/0.66  fof(f81,plain,(
% 2.06/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f46])).
% 2.06/0.66  fof(f46,plain,(
% 2.06/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.66    inference(flattening,[],[f45])).
% 2.06/0.66  fof(f45,plain,(
% 2.06/0.66    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.06/0.66    inference(ennf_transformation,[],[f16])).
% 2.06/0.66  fof(f16,axiom,(
% 2.06/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.06/0.66  fof(f1909,plain,(
% 2.06/0.66    sK1 != k2_xboole_0(sK1,k1_xboole_0) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(backward_demodulation,[],[f905,f1901])).
% 2.06/0.66  fof(f1901,plain,(
% 2.06/0.66    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k1_xboole_0)),
% 2.06/0.66    inference(backward_demodulation,[],[f1248,f1871])).
% 2.06/0.66  fof(f1871,plain,(
% 2.06/0.66    k2_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(superposition,[],[f85,f1804])).
% 2.06/0.66  fof(f1804,plain,(
% 2.06/0.66    k1_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),sK1)),
% 2.06/0.66    inference(forward_demodulation,[],[f1774,f139])).
% 2.06/0.66  fof(f1774,plain,(
% 2.06/0.66    k4_xboole_0(k2_tops_1(sK0,sK1),sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(superposition,[],[f463,f897])).
% 2.06/0.66  fof(f897,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(k2_tops_1(sK0,sK1),sK1))),
% 2.06/0.66    inference(superposition,[],[f110,f885])).
% 2.06/0.66  fof(f885,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f880,f57])).
% 2.06/0.66  fof(f880,plain,(
% 2.06/0.66    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.06/0.66    inference(duplicate_literal_removal,[],[f877])).
% 2.06/0.66  fof(f877,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f876,f161])).
% 2.06/0.66  fof(f161,plain,(
% 2.06/0.66    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.06/0.66    inference(backward_demodulation,[],[f59,f159])).
% 2.06/0.66  fof(f159,plain,(
% 2.06/0.66    ( ! [X9] : (k7_subset_1(u1_struct_0(sK0),sK1,X9) = k4_xboole_0(sK1,X9)) )),
% 2.06/0.66    inference(resolution,[],[f61,f58])).
% 2.06/0.66  fof(f61,plain,(
% 2.06/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f31])).
% 2.06/0.66  fof(f31,plain,(
% 2.06/0.66    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f17])).
% 2.06/0.66  fof(f17,axiom,(
% 2.06/0.66    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.06/0.66  fof(f59,plain,(
% 2.06/0.66    v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.06/0.66    inference(cnf_transformation,[],[f52])).
% 2.06/0.66  fof(f876,plain,(
% 2.06/0.66    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(forward_demodulation,[],[f871,f235])).
% 2.06/0.66  fof(f235,plain,(
% 2.06/0.66    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f234,f57])).
% 2.06/0.66  fof(f234,plain,(
% 2.06/0.66    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(forward_demodulation,[],[f231,f159])).
% 2.06/0.66  fof(f231,plain,(
% 2.06/0.66    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f62,f58])).
% 2.06/0.66  fof(f62,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f32])).
% 2.06/0.66  fof(f32,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(ennf_transformation,[],[f26])).
% 2.06/0.66  fof(f26,axiom,(
% 2.06/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.06/0.66  fof(f871,plain,(
% 2.06/0.66    ~v4_pre_topc(sK1,sK0) | k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f184,f58])).
% 2.06/0.66  fof(f184,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X0,X1) | k2_tops_1(X1,X0) = k4_xboole_0(X0,k4_xboole_0(X0,k2_tops_1(X1,X0))) | ~l1_pre_topc(X1)) )),
% 2.06/0.66    inference(forward_demodulation,[],[f180,f89])).
% 2.06/0.66  fof(f180,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~v4_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_tops_1(X1,X0) = k4_xboole_0(k2_tops_1(X1,X0),k4_xboole_0(k2_tops_1(X1,X0),X0))) )),
% 2.06/0.66    inference(resolution,[],[f64,f88])).
% 2.06/0.66  fof(f88,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 2.06/0.66    inference(definition_unfolding,[],[f79,f74])).
% 2.06/0.66  fof(f79,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f44])).
% 2.06/0.66  fof(f44,plain,(
% 2.06/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.06/0.66    inference(ennf_transformation,[],[f5])).
% 2.06/0.66  fof(f5,axiom,(
% 2.06/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.06/0.66  fof(f64,plain,(
% 2.06/0.66    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f36])).
% 2.06/0.66  fof(f36,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(flattening,[],[f35])).
% 2.06/0.66  fof(f35,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(ennf_transformation,[],[f25])).
% 2.06/0.66  fof(f25,axiom,(
% 2.06/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).
% 2.06/0.66  fof(f110,plain,(
% 2.06/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(k4_xboole_0(X2,X3),X2))) )),
% 2.06/0.66    inference(resolution,[],[f88,f75])).
% 2.06/0.66  fof(f463,plain,(
% 2.06/0.66    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 2.06/0.66    inference(superposition,[],[f110,f89])).
% 2.06/0.66  fof(f85,plain,(
% 2.06/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f8])).
% 2.06/0.66  fof(f8,axiom,(
% 2.06/0.66    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.06/0.66  fof(f1248,plain,(
% 2.06/0.66    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f1247,f57])).
% 2.06/0.66  fof(f1247,plain,(
% 2.06/0.66    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(forward_demodulation,[],[f1242,f249])).
% 2.06/0.66  fof(f249,plain,(
% 2.06/0.66    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f241,f57])).
% 2.06/0.66  fof(f241,plain,(
% 2.06/0.66    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.66    inference(resolution,[],[f65,f58])).
% 2.06/0.66  fof(f65,plain,(
% 2.06/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f37])).
% 2.06/0.66  fof(f37,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(ennf_transformation,[],[f24])).
% 2.06/0.66  fof(f24,axiom,(
% 2.06/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.06/0.66  fof(f1242,plain,(
% 2.06/0.66    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f255,f58])).
% 2.06/0.66  fof(f255,plain,(
% 2.06/0.66    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X2)) = k2_xboole_0(sK1,k2_tops_1(sK0,X2)) | ~l1_pre_topc(sK0)) )),
% 2.06/0.66    inference(resolution,[],[f204,f63])).
% 2.06/0.66  fof(f63,plain,(
% 2.06/0.66    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f34])).
% 2.06/0.66  fof(f34,plain,(
% 2.06/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(flattening,[],[f33])).
% 2.06/0.66  fof(f33,plain,(
% 2.06/0.66    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.06/0.66    inference(ennf_transformation,[],[f22])).
% 2.06/0.66  fof(f22,axiom,(
% 2.06/0.66    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.06/0.66  fof(f204,plain,(
% 2.06/0.66    ( ! [X12] : (~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK1,X12) = k2_xboole_0(sK1,X12)) )),
% 2.06/0.66    inference(resolution,[],[f81,f58])).
% 2.06/0.66  fof(f905,plain,(
% 2.06/0.66    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.06/0.66    inference(resolution,[],[f901,f68])).
% 2.06/0.66  fof(f68,plain,(
% 2.06/0.66    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.66    inference(cnf_transformation,[],[f40])).
% 2.06/0.66  fof(f40,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(flattening,[],[f39])).
% 2.06/0.66  fof(f39,plain,(
% 2.06/0.66    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.66    inference(ennf_transformation,[],[f21])).
% 2.06/0.66  fof(f21,axiom,(
% 2.06/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.06/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.06/0.66  fof(f901,plain,(
% 2.06/0.66    ~v4_pre_topc(sK1,sK0)),
% 2.06/0.66    inference(trivial_inequality_removal,[],[f886])).
% 2.06/0.66  fof(f886,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.06/0.66    inference(backward_demodulation,[],[f160,f885])).
% 2.06/0.66  fof(f160,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.06/0.66    inference(backward_demodulation,[],[f60,f159])).
% 2.06/0.66  fof(f60,plain,(
% 2.06/0.66    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.06/0.66    inference(cnf_transformation,[],[f52])).
% 2.06/0.66  % SZS output end Proof for theBenchmark
% 2.06/0.66  % (1411)------------------------------
% 2.06/0.66  % (1411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.06/0.66  % (1411)Termination reason: Refutation
% 2.06/0.66  
% 2.06/0.66  % (1411)Memory used [KB]: 2686
% 2.06/0.66  % (1411)Time elapsed: 0.229 s
% 2.06/0.66  % (1411)------------------------------
% 2.06/0.66  % (1411)------------------------------
% 2.06/0.67  % (1400)Success in time 0.312 s
%------------------------------------------------------------------------------
