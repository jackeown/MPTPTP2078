%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:50 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 585 expanded)
%              Number of leaves         :   19 ( 139 expanded)
%              Depth                    :   22
%              Number of atoms          :  208 (1765 expanded)
%              Number of equality atoms :   74 ( 493 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2143,plain,(
    $false ),
    inference(global_subsumption,[],[f2062,f2142])).

fof(f2142,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2112,f2140])).

fof(f2140,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2114,f982])).

fof(f982,plain,(
    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f55,f53,f974])).

fof(f974,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f60,f699])).

fof(f699,plain,(
    ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f53,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f83,f67])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f2114,plain,(
    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2083,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f74,f67])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2083,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f2076,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2076,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f546,f2066])).

fof(f2066,plain,(
    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1049,f2064])).

fof(f2064,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f55,f53,f2061,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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

fof(f2061,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(global_subsumption,[],[f55,f54,f53,f2060])).

fof(f2060,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f2059])).

fof(f2059,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f2058])).

fof(f2058,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f62,f2057])).

fof(f2057,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2056,f1049])).

fof(f2056,plain,
    ( sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))
    | v4_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2053,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f2053,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f105,f761])).

fof(f761,plain,
    ( sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))))
    | v4_pre_topc(sK1,sK0) ),
    inference(superposition,[],[f125,f703])).

fof(f703,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f51,f699])).

fof(f51,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f125,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(forward_demodulation,[],[f107,f66])).

fof(f107,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f72,f69,f68,f67])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f69,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f105,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f70,f69,f69,f69])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f1049,plain,(
    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f911,f1042])).

fof(f1042,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f55,f53,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f911,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f53,f775,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f86,f69])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f775,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f55,f53,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f546,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f104,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f85,f67,f69])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2112,plain,(
    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f2083,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2062,plain,(
    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f2061,f1110])).

fof(f1110,plain,
    ( k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f704,f1097])).

fof(f1097,plain,(
    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1071,f108])).

fof(f1071,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(superposition,[],[f65,f982])).

fof(f65,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f704,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f52,f699])).

fof(f52,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (29510)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.48  % (29526)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (29506)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (29508)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (29511)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (29525)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (29504)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (29507)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (29530)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (29505)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (29517)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (29518)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (29522)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (29524)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (29532)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (29509)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (29520)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (29523)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (29527)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (29516)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (29525)Refutation not found, incomplete strategy% (29525)------------------------------
% 0.21/0.55  % (29525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29515)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (29528)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (29503)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (29513)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (29512)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (29525)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (29525)Memory used [KB]: 10746
% 0.21/0.55  % (29525)Time elapsed: 0.101 s
% 0.21/0.55  % (29525)------------------------------
% 0.21/0.55  % (29525)------------------------------
% 0.21/0.55  % (29520)Refutation not found, incomplete strategy% (29520)------------------------------
% 0.21/0.55  % (29520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29529)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (29514)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (29519)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (29521)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (29531)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (29520)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (29520)Memory used [KB]: 10618
% 0.21/0.56  % (29520)Time elapsed: 0.138 s
% 0.21/0.56  % (29520)------------------------------
% 0.21/0.56  % (29520)------------------------------
% 2.20/0.67  % (29527)Refutation found. Thanks to Tanya!
% 2.20/0.67  % SZS status Theorem for theBenchmark
% 2.20/0.68  % SZS output start Proof for theBenchmark
% 2.20/0.68  fof(f2143,plain,(
% 2.20/0.68    $false),
% 2.20/0.68    inference(global_subsumption,[],[f2062,f2142])).
% 2.20/0.68  fof(f2142,plain,(
% 2.20/0.68    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.20/0.68    inference(forward_demodulation,[],[f2112,f2140])).
% 2.20/0.68  fof(f2140,plain,(
% 2.20/0.68    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.20/0.68    inference(forward_demodulation,[],[f2114,f982])).
% 2.20/0.68  fof(f982,plain,(
% 2.20/0.68    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.20/0.68    inference(global_subsumption,[],[f55,f53,f974])).
% 2.20/0.68  fof(f974,plain,(
% 2.20/0.68    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.20/0.68    inference(superposition,[],[f60,f699])).
% 2.20/0.68  fof(f699,plain,(
% 2.20/0.68    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 2.20/0.68    inference(unit_resulting_resolution,[],[f53,f109])).
% 2.20/0.68  fof(f109,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.68    inference(definition_unfolding,[],[f83,f67])).
% 2.20/0.68  fof(f67,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f20])).
% 2.20/0.68  fof(f20,axiom,(
% 2.20/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.20/0.68  fof(f83,plain,(
% 2.20/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f46])).
% 2.20/0.68  fof(f46,plain,(
% 2.20/0.68    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.68    inference(ennf_transformation,[],[f21])).
% 2.20/0.68  fof(f21,axiom,(
% 2.20/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.20/0.68  fof(f60,plain,(
% 2.20/0.68    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.20/0.68    inference(cnf_transformation,[],[f35])).
% 2.20/0.68  fof(f35,plain,(
% 2.20/0.68    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.20/0.68    inference(ennf_transformation,[],[f29])).
% 2.20/0.68  fof(f29,axiom,(
% 2.20/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.20/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.20/0.68  fof(f53,plain,(
% 2.20/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.20/0.68    inference(cnf_transformation,[],[f33])).
% 2.20/0.68  fof(f33,plain,(
% 2.20/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.20/0.68    inference(flattening,[],[f32])).
% 2.20/0.68  fof(f32,plain,(
% 2.20/0.68    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.20/0.68    inference(ennf_transformation,[],[f31])).
% 2.20/0.69  fof(f31,negated_conjecture,(
% 2.20/0.69    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.20/0.69    inference(negated_conjecture,[],[f30])).
% 2.20/0.69  fof(f30,conjecture,(
% 2.20/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.20/0.69  fof(f55,plain,(
% 2.20/0.69    l1_pre_topc(sK0)),
% 2.20/0.69    inference(cnf_transformation,[],[f33])).
% 2.20/0.69  fof(f2114,plain,(
% 2.20/0.69    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f2083,f108])).
% 2.20/0.69  fof(f108,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(definition_unfolding,[],[f74,f67])).
% 2.20/0.69  fof(f74,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f40])).
% 2.20/0.69  fof(f40,plain,(
% 2.20/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f15])).
% 2.20/0.69  fof(f15,axiom,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.20/0.69  fof(f2083,plain,(
% 2.20/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f2076,f80])).
% 2.20/0.69  fof(f80,plain,(
% 2.20/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f23])).
% 2.20/0.69  fof(f23,axiom,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.20/0.69  fof(f2076,plain,(
% 2.20/0.69    r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.20/0.69    inference(superposition,[],[f546,f2066])).
% 2.20/0.69  fof(f2066,plain,(
% 2.20/0.69    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.20/0.69    inference(backward_demodulation,[],[f1049,f2064])).
% 2.20/0.69  fof(f2064,plain,(
% 2.20/0.69    sK1 = k2_pre_topc(sK0,sK1)),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f55,f53,f2061,f63])).
% 2.20/0.69  fof(f63,plain,(
% 2.20/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 2.20/0.69    inference(cnf_transformation,[],[f38])).
% 2.20/0.69  fof(f38,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.20/0.69    inference(flattening,[],[f37])).
% 2.20/0.69  fof(f37,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.20/0.69    inference(ennf_transformation,[],[f25])).
% 2.20/0.69  fof(f25,axiom,(
% 2.20/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.20/0.69  fof(f2061,plain,(
% 2.20/0.69    v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(global_subsumption,[],[f55,f54,f53,f2060])).
% 2.20/0.69  fof(f2060,plain,(
% 2.20/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(trivial_inequality_removal,[],[f2059])).
% 2.20/0.69  fof(f2059,plain,(
% 2.20/0.69    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(duplicate_literal_removal,[],[f2058])).
% 2.20/0.69  fof(f2058,plain,(
% 2.20/0.69    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(superposition,[],[f62,f2057])).
% 2.20/0.69  fof(f2057,plain,(
% 2.20/0.69    sK1 = k2_pre_topc(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(forward_demodulation,[],[f2056,f1049])).
% 2.20/0.69  fof(f2056,plain,(
% 2.20/0.69    sK1 = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(forward_demodulation,[],[f2053,f66])).
% 2.20/0.69  fof(f66,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f13])).
% 2.20/0.69  fof(f13,axiom,(
% 2.20/0.69    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.20/0.69  fof(f2053,plain,(
% 2.20/0.69    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),sK1)) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(superposition,[],[f105,f761])).
% 2.20/0.69  fof(f761,plain,(
% 2.20/0.69    sK1 = k3_tarski(k2_tarski(k2_tops_1(sK0,sK1),k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))))) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(superposition,[],[f125,f703])).
% 2.20/0.69  fof(f703,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) = k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(backward_demodulation,[],[f51,f699])).
% 2.20/0.69  fof(f51,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(cnf_transformation,[],[f33])).
% 2.20/0.69  fof(f125,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_tarski(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))) = X0) )),
% 2.20/0.69    inference(forward_demodulation,[],[f107,f66])).
% 2.20/0.69  fof(f107,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0) )),
% 2.20/0.69    inference(definition_unfolding,[],[f72,f69,f68,f67])).
% 2.20/0.69  fof(f68,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f22])).
% 2.20/0.69  fof(f22,axiom,(
% 2.20/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.20/0.69  fof(f69,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f14])).
% 2.20/0.69  fof(f14,axiom,(
% 2.20/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.20/0.69  fof(f72,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.20/0.69    inference(cnf_transformation,[],[f11])).
% 2.20/0.69  fof(f11,axiom,(
% 2.20/0.69    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.20/0.69  fof(f105,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k3_tarski(k2_tarski(X0,X1))))) )),
% 2.20/0.69    inference(definition_unfolding,[],[f70,f69,f69,f69])).
% 2.20/0.69  fof(f70,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f12])).
% 2.20/0.69  fof(f12,axiom,(
% 2.20/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 2.20/0.69  fof(f62,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f38])).
% 2.20/0.69  fof(f54,plain,(
% 2.20/0.69    v2_pre_topc(sK0)),
% 2.20/0.69    inference(cnf_transformation,[],[f33])).
% 2.20/0.69  fof(f1049,plain,(
% 2.20/0.69    k2_pre_topc(sK0,sK1) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.20/0.69    inference(backward_demodulation,[],[f911,f1042])).
% 2.20/0.69  fof(f1042,plain,(
% 2.20/0.69    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f55,f53,f61])).
% 2.20/0.69  fof(f61,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f36])).
% 2.20/0.69  fof(f36,plain,(
% 2.20/0.69    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.20/0.69    inference(ennf_transformation,[],[f28])).
% 2.20/0.69  fof(f28,axiom,(
% 2.20/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.20/0.69  fof(f911,plain,(
% 2.20/0.69    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1)))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f53,f775,f112])).
% 2.20/0.69  fof(f112,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(definition_unfolding,[],[f86,f69])).
% 2.20/0.69  fof(f86,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f50])).
% 2.20/0.69  fof(f50,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(flattening,[],[f49])).
% 2.20/0.69  fof(f49,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.20/0.69    inference(ennf_transformation,[],[f19])).
% 2.20/0.69  fof(f19,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.20/0.69  fof(f775,plain,(
% 2.20/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f55,f53,f76])).
% 2.20/0.69  fof(f76,plain,(
% 2.20/0.69    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f43])).
% 2.20/0.69  fof(f43,plain,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.20/0.69    inference(flattening,[],[f42])).
% 2.20/0.69  fof(f42,plain,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f26])).
% 2.20/0.69  fof(f26,axiom,(
% 2.20/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.20/0.69  fof(f546,plain,(
% 2.20/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X0)))) )),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f104,f111])).
% 2.20/0.69  fof(f111,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.20/0.69    inference(definition_unfolding,[],[f85,f67,f69])).
% 2.20/0.69  fof(f85,plain,(
% 2.20/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f48])).
% 2.20/0.69  fof(f48,plain,(
% 2.20/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.20/0.69    inference(ennf_transformation,[],[f10])).
% 2.20/0.69  fof(f10,axiom,(
% 2.20/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.20/0.69  fof(f104,plain,(
% 2.20/0.69    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.20/0.69    inference(definition_unfolding,[],[f64,f67])).
% 2.20/0.69  fof(f64,plain,(
% 2.20/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.20/0.69    inference(cnf_transformation,[],[f7])).
% 2.20/0.69  fof(f7,axiom,(
% 2.20/0.69    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.20/0.69  fof(f2112,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f2083,f75])).
% 2.20/0.69  fof(f75,plain,(
% 2.20/0.69    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f41])).
% 2.20/0.69  fof(f41,plain,(
% 2.20/0.69    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.69    inference(ennf_transformation,[],[f18])).
% 2.20/0.69  fof(f18,axiom,(
% 2.20/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.20/0.69  fof(f2062,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f2061,f1110])).
% 2.20/0.69  fof(f1110,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) != k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(backward_demodulation,[],[f704,f1097])).
% 2.20/0.69  fof(f1097,plain,(
% 2.20/0.69    k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))),
% 2.20/0.69    inference(unit_resulting_resolution,[],[f1071,f108])).
% 2.20/0.69  fof(f1071,plain,(
% 2.20/0.69    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.20/0.69    inference(superposition,[],[f65,f982])).
% 2.20/0.69  fof(f65,plain,(
% 2.20/0.69    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.20/0.69    inference(cnf_transformation,[],[f17])).
% 2.20/0.69  fof(f17,axiom,(
% 2.20/0.69    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.20/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.20/0.69  fof(f704,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) != k6_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(backward_demodulation,[],[f52,f699])).
% 2.20/0.69  fof(f52,plain,(
% 2.20/0.69    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.20/0.69    inference(cnf_transformation,[],[f33])).
% 2.20/0.69  % SZS output end Proof for theBenchmark
% 2.20/0.69  % (29527)------------------------------
% 2.20/0.69  % (29527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (29527)Termination reason: Refutation
% 2.20/0.69  
% 2.20/0.69  % (29527)Memory used [KB]: 8315
% 2.20/0.69  % (29527)Time elapsed: 0.251 s
% 2.20/0.69  % (29527)------------------------------
% 2.20/0.69  % (29527)------------------------------
% 2.20/0.69  % (29502)Success in time 0.331 s
%------------------------------------------------------------------------------
