%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:35 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 243 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :   18
%              Number of atoms          :  195 (1050 expanded)
%              Number of equality atoms :   42 (  85 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1984,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1983,f72])).

fof(f72,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f55,f48])).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1983,plain,(
    ~ r1_tarski(sK1,sK1) ),
    inference(forward_demodulation,[],[f1982,f49])).

fof(f49,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f1982,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1981,f1840])).

fof(f1840,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1837,f150])).

fof(f150,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f44])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f147,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f1837,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(resolution,[],[f1836,f46])).

fof(f46,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f1836,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1833,f44])).

fof(f1833,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f402,f45])).

fof(f402,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | k1_xboole_0 = k1_tops_1(X3,X2)
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(X2,k2_tops_1(X3,X2)) ) ),
    inference(superposition,[],[f169,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(forward_demodulation,[],[f126,f48])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0))
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f69,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f169,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f51,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f1981,plain,(
    ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1980,f44])).

fof(f1980,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1979,f45])).

fof(f1979,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1912,f1842])).

fof(f1842,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f1841])).

fof(f1841,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f154,f1840])).

fof(f154,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f151,f44])).

fof(f151,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1912,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f599,f403])).

fof(f403,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_tops_1(X1,X0)) = k4_xboole_0(X0,k1_tops_1(X1,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1) ) ),
    inference(superposition,[],[f60,f169])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f599,plain,(
    ! [X21] :
      ( ~ r1_tarski(sK1,k3_xboole_0(X21,k2_tops_1(sK0,sK1)))
      | ~ v2_tops_1(sK1,sK0) ) ),
    inference(superposition,[],[f122,f174])).

fof(f174,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f89,f59])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f59,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f122,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,k3_xboole_0(k2_tops_1(sK0,sK1),X3))
      | ~ v2_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f116,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_tops_1(sK0,sK1))
      | ~ r1_tarski(sK1,X0)
      | ~ v2_tops_1(sK1,sK0) ) ),
    inference(resolution,[],[f70,f47])).

fof(f47,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.43  % (19621)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.46  % (19630)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (19626)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.46  % (19622)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (19632)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (19629)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.48  % (19634)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.48  % (19623)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.48  % (19619)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.48  % (19633)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.49  % (19625)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (19624)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.49  % (19620)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.49  % (19627)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.50  % (19631)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.50  % (19636)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.37/0.53  % (19635)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.37/0.53  % (19628)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.49/0.55  % (19622)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f1984,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(subsumption_resolution,[],[f1983,f72])).
% 1.49/0.55  fof(f72,plain,(
% 1.49/0.55    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.49/0.55    inference(superposition,[],[f55,f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,axiom,(
% 1.49/0.55    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.49/0.55  fof(f1983,plain,(
% 1.49/0.55    ~r1_tarski(sK1,sK1)),
% 1.49/0.55    inference(forward_demodulation,[],[f1982,f49])).
% 1.49/0.55  fof(f49,plain,(
% 1.49/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.49/0.55  fof(f1982,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_xboole_0))),
% 1.49/0.55    inference(forward_demodulation,[],[f1981,f1840])).
% 1.49/0.55  fof(f1840,plain,(
% 1.49/0.55    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1837,f150])).
% 1.49/0.55  fof(f150,plain,(
% 1.49/0.55    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(subsumption_resolution,[],[f147,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    l1_pre_topc(sK0)),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f41,plain,(
% 1.49/0.55    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 1.49/0.55  fof(f39,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f40,plain,(
% 1.49/0.55    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.49/0.55    inference(flattening,[],[f37])).
% 1.49/0.55  fof(f37,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f24])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f23])).
% 1.49/0.55  fof(f23,negated_conjecture,(
% 1.49/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.49/0.55    inference(negated_conjecture,[],[f22])).
% 1.49/0.55  fof(f22,conjecture,(
% 1.49/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 1.49/0.55  fof(f147,plain,(
% 1.49/0.55    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.49/0.55    inference(resolution,[],[f52,f45])).
% 1.49/0.55  fof(f45,plain,(
% 1.49/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f52,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f42])).
% 1.49/0.55  fof(f42,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.55    inference(nnf_transformation,[],[f27])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f21])).
% 1.49/0.55  fof(f21,axiom,(
% 1.49/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.49/0.55  fof(f1837,plain,(
% 1.49/0.55    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(resolution,[],[f1836,f46])).
% 1.49/0.55  fof(f46,plain,(
% 1.49/0.55    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f1836,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1833,f44])).
% 1.49/0.55  fof(f1833,plain,(
% 1.49/0.55    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.49/0.55    inference(resolution,[],[f402,f45])).
% 1.49/0.55  fof(f402,plain,(
% 1.49/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | k1_xboole_0 = k1_tops_1(X3,X2) | ~l1_pre_topc(X3) | ~r1_tarski(X2,k2_tops_1(X3,X2))) )),
% 1.49/0.55    inference(superposition,[],[f169,f132])).
% 1.49/0.55  fof(f132,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(forward_demodulation,[],[f126,f48])).
% 1.49/0.55  fof(f126,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,k1_xboole_0)) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.49/0.55    inference(resolution,[],[f69,f54])).
% 1.49/0.55  fof(f54,plain,(
% 1.49/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f28])).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.49/0.55  fof(f69,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f34])).
% 1.49/0.55  fof(f34,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.49/0.55  fof(f169,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 1.49/0.55    inference(duplicate_literal_removal,[],[f166])).
% 1.49/0.55  fof(f166,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k4_xboole_0(X3,k2_tops_1(X2,X3)) = k1_tops_1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.49/0.55    inference(superposition,[],[f51,f68])).
% 1.49/0.55  fof(f68,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f33])).
% 1.49/0.55  fof(f33,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.49/0.55    inference(ennf_transformation,[],[f16])).
% 1.49/0.55  fof(f16,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.49/0.55  fof(f51,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.55    inference(ennf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,axiom,(
% 1.49/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.49/0.55  fof(f1981,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 1.49/0.55    inference(subsumption_resolution,[],[f1980,f44])).
% 1.49/0.55  fof(f1980,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1979,f45])).
% 1.49/0.55  fof(f1979,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.55    inference(subsumption_resolution,[],[f1912,f1842])).
% 1.49/0.55  fof(f1842,plain,(
% 1.49/0.55    v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f1841])).
% 1.49/0.55  fof(f1841,plain,(
% 1.49/0.55    k1_xboole_0 != k1_xboole_0 | v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(backward_demodulation,[],[f154,f1840])).
% 1.49/0.55  fof(f154,plain,(
% 1.49/0.55    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(subsumption_resolution,[],[f151,f44])).
% 1.49/0.55  fof(f151,plain,(
% 1.49/0.55    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.49/0.55    inference(resolution,[],[f53,f45])).
% 1.49/0.55  fof(f53,plain,(
% 1.49/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f42])).
% 1.49/0.55  fof(f1912,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~v2_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.49/0.55    inference(superposition,[],[f599,f403])).
% 1.49/0.55  fof(f403,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,k2_tops_1(X1,X0)) = k4_xboole_0(X0,k1_tops_1(X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) )),
% 1.49/0.55    inference(superposition,[],[f60,f169])).
% 1.49/0.55  fof(f60,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f11])).
% 1.49/0.55  fof(f11,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.49/0.55  fof(f599,plain,(
% 1.49/0.55    ( ! [X21] : (~r1_tarski(sK1,k3_xboole_0(X21,k2_tops_1(sK0,sK1))) | ~v2_tops_1(sK1,sK0)) )),
% 1.49/0.55    inference(superposition,[],[f122,f174])).
% 1.49/0.55  fof(f174,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 1.49/0.55    inference(superposition,[],[f89,f59])).
% 1.49/0.55  fof(f59,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.49/0.55  fof(f89,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.49/0.55    inference(superposition,[],[f59,f57])).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.49/0.55  fof(f122,plain,(
% 1.49/0.55    ( ! [X3] : (~r1_tarski(sK1,k3_xboole_0(k2_tops_1(sK0,sK1),X3)) | ~v2_tops_1(sK1,sK0)) )),
% 1.49/0.55    inference(resolution,[],[f116,f56])).
% 1.49/0.55  fof(f56,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.49/0.55  fof(f116,plain,(
% 1.49/0.55    ( ! [X0] : (~r1_tarski(X0,k2_tops_1(sK0,sK1)) | ~r1_tarski(sK1,X0) | ~v2_tops_1(sK1,sK0)) )),
% 1.49/0.55    inference(resolution,[],[f70,f47])).
% 1.49/0.55  fof(f47,plain,(
% 1.49/0.55    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.49/0.55    inference(cnf_transformation,[],[f41])).
% 1.49/0.55  fof(f70,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.49/0.55    inference(flattening,[],[f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.49/0.55    inference(ennf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (19622)------------------------------
% 1.49/0.55  % (19622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (19622)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (19622)Memory used [KB]: 2558
% 1.49/0.55  % (19622)Time elapsed: 0.129 s
% 1.49/0.55  % (19622)------------------------------
% 1.49/0.55  % (19622)------------------------------
% 1.49/0.55  % (19618)Success in time 0.193 s
%------------------------------------------------------------------------------
