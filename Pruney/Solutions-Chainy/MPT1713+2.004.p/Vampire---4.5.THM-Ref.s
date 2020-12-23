%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:50 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 286 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  218 (1352 expanded)
%              Number of equality atoms :   29 (  44 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(subsumption_resolution,[],[f316,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f316,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f89,f314])).

fof(f314,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f313,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f104,f91])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f63,f68])).

fof(f68,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f60,f40])).

fof(f40,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f104,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f64,f90])).

fof(f90,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f63,f40])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f57,f58,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f313,plain,(
    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f312,f162])).

fof(f162,plain,(
    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,(
    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f160,f82])).

fof(f82,plain,(
    k2_struct_0(sK1) = u1_struct_0(sK1) ),
    inference(resolution,[],[f80,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f80,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f73,f44])).

% (22673)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f73,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f71,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f55,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f160,plain,(
    r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f159,f80])).

fof(f159,plain,
    ( ~ l1_struct_0(sK1)
    | r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f151,f99])).

fof(f99,plain,(
    r1_tsep_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f98,f78])).

fof(f78,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f72,f44])).

fof(f72,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f71,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2) ),
    inference(subsumption_resolution,[],[f97,f80])).

fof(f97,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK1,sK2) ),
    inference(resolution,[],[f61,f31])).

fof(f31,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f151,plain,(
    ! [X1] :
      ( ~ r1_tsep_1(X1,sK2)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK2)) ) ),
    inference(forward_demodulation,[],[f148,f81])).

fof(f81,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f78,f41])).

fof(f148,plain,(
    ! [X1] :
      ( ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2))
      | ~ r1_tsep_1(X1,sK2) ) ),
    inference(resolution,[],[f43,f78])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f312,plain,(
    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))) ),
    inference(resolution,[],[f232,f34])).

fof(f34,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f232,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK2)
      | k2_struct_0(X1) = k4_xboole_0(k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),k2_struct_0(sK2))) ) ),
    inference(resolution,[],[f181,f72])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f180,f55])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1))) ) ),
    inference(resolution,[],[f54,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f59,f58])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f89,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f88,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f87,f80])).

fof(f87,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f56,f82])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:01:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.50/0.58  % (22658)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.58  % (22663)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.76/0.59  % (22657)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.76/0.59  % (22644)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.76/0.59  % (22665)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.76/0.59  % (22649)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.76/0.59  % (22648)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.76/0.60  % (22658)Refutation not found, incomplete strategy% (22658)------------------------------
% 1.76/0.60  % (22658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (22658)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (22658)Memory used [KB]: 6268
% 1.76/0.60  % (22658)Time elapsed: 0.176 s
% 1.76/0.60  % (22658)------------------------------
% 1.76/0.60  % (22658)------------------------------
% 1.76/0.60  % (22655)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.76/0.60  % (22647)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.76/0.60  % (22650)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.76/0.60  % (22665)Refutation not found, incomplete strategy% (22665)------------------------------
% 1.76/0.60  % (22665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (22665)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.60  
% 1.76/0.60  % (22665)Memory used [KB]: 10746
% 1.76/0.60  % (22665)Time elapsed: 0.095 s
% 1.76/0.60  % (22665)------------------------------
% 1.76/0.60  % (22665)------------------------------
% 1.76/0.61  % (22670)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.76/0.61  % (22672)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.76/0.62  % (22645)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.76/0.62  % (22646)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.76/0.62  % (22649)Refutation found. Thanks to Tanya!
% 1.76/0.62  % SZS status Theorem for theBenchmark
% 1.76/0.62  % SZS output start Proof for theBenchmark
% 1.76/0.62  fof(f336,plain,(
% 1.76/0.62    $false),
% 1.76/0.62    inference(subsumption_resolution,[],[f316,f39])).
% 1.76/0.62  fof(f39,plain,(
% 1.76/0.62    v1_xboole_0(k1_xboole_0)),
% 1.76/0.62    inference(cnf_transformation,[],[f2])).
% 1.76/0.62  fof(f2,axiom,(
% 1.76/0.62    v1_xboole_0(k1_xboole_0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.76/0.62  fof(f316,plain,(
% 1.76/0.62    ~v1_xboole_0(k1_xboole_0)),
% 1.76/0.62    inference(backward_demodulation,[],[f89,f314])).
% 1.76/0.62  fof(f314,plain,(
% 1.76/0.62    k1_xboole_0 = k2_struct_0(sK1)),
% 1.76/0.62    inference(forward_demodulation,[],[f313,f114])).
% 1.76/0.62  fof(f114,plain,(
% 1.76/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.76/0.62    inference(forward_demodulation,[],[f104,f91])).
% 1.76/0.62  fof(f91,plain,(
% 1.76/0.62    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.76/0.62    inference(resolution,[],[f63,f68])).
% 1.76/0.62  fof(f68,plain,(
% 1.76/0.62    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.76/0.62    inference(resolution,[],[f60,f40])).
% 1.76/0.62  fof(f40,plain,(
% 1.76/0.62    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f6])).
% 1.76/0.62  fof(f6,axiom,(
% 1.76/0.62    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.76/0.62  fof(f60,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f28])).
% 1.76/0.62  fof(f28,plain,(
% 1.76/0.62    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.76/0.62    inference(ennf_transformation,[],[f3])).
% 1.76/0.62  fof(f3,axiom,(
% 1.76/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.76/0.62  fof(f63,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f7])).
% 1.76/0.62  fof(f7,axiom,(
% 1.76/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.76/0.62  fof(f104,plain,(
% 1.76/0.62    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,X0)) )),
% 1.76/0.62    inference(superposition,[],[f64,f90])).
% 1.76/0.62  fof(f90,plain,(
% 1.76/0.62    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.76/0.62    inference(resolution,[],[f63,f40])).
% 1.76/0.62  fof(f64,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.76/0.62    inference(definition_unfolding,[],[f57,f58,f58])).
% 1.76/0.62  fof(f58,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.76/0.62    inference(cnf_transformation,[],[f5])).
% 1.76/0.62  fof(f5,axiom,(
% 1.76/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.76/0.62  fof(f57,plain,(
% 1.76/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f1])).
% 1.76/0.62  fof(f1,axiom,(
% 1.76/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.76/0.62  fof(f313,plain,(
% 1.76/0.62    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK1))),
% 1.76/0.62    inference(forward_demodulation,[],[f312,f162])).
% 1.76/0.62  fof(f162,plain,(
% 1.76/0.62    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.76/0.62    inference(resolution,[],[f161,f63])).
% 1.76/0.62  fof(f161,plain,(
% 1.76/0.62    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))),
% 1.76/0.62    inference(forward_demodulation,[],[f160,f82])).
% 1.76/0.62  fof(f82,plain,(
% 1.76/0.62    k2_struct_0(sK1) = u1_struct_0(sK1)),
% 1.76/0.62    inference(resolution,[],[f80,f41])).
% 1.76/0.62  fof(f41,plain,(
% 1.76/0.62    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f20])).
% 1.76/0.62  fof(f20,plain,(
% 1.76/0.62    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f8])).
% 1.76/0.62  fof(f8,axiom,(
% 1.76/0.62    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.76/0.62  fof(f80,plain,(
% 1.76/0.62    l1_struct_0(sK1)),
% 1.76/0.62    inference(resolution,[],[f73,f44])).
% 1.76/0.62  % (22673)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.76/0.62  fof(f44,plain,(
% 1.76/0.62    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f22])).
% 1.76/0.62  fof(f22,plain,(
% 1.76/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f10])).
% 1.76/0.62  fof(f10,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.76/0.62  fof(f73,plain,(
% 1.76/0.62    l1_pre_topc(sK1)),
% 1.76/0.62    inference(resolution,[],[f71,f36])).
% 1.76/0.62  fof(f36,plain,(
% 1.76/0.62    m1_pre_topc(sK1,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f19,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.76/0.62    inference(flattening,[],[f18])).
% 1.76/0.62  fof(f18,plain,(
% 1.76/0.62    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f17])).
% 1.76/0.62  fof(f17,plain,(
% 1.76/0.62    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.76/0.62    inference(pure_predicate_removal,[],[f16])).
% 1.76/0.62  fof(f16,negated_conjecture,(
% 1.76/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.76/0.62    inference(negated_conjecture,[],[f15])).
% 1.76/0.62  fof(f15,conjecture,(
% 1.76/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 1.76/0.62  fof(f71,plain,(
% 1.76/0.62    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.76/0.62    inference(resolution,[],[f55,f38])).
% 1.76/0.62  fof(f38,plain,(
% 1.76/0.62    l1_pre_topc(sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f55,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f24])).
% 1.76/0.62  fof(f24,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f11])).
% 1.76/0.62  fof(f11,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.76/0.62  fof(f160,plain,(
% 1.76/0.62    r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2))),
% 1.76/0.62    inference(subsumption_resolution,[],[f159,f80])).
% 1.76/0.62  fof(f159,plain,(
% 1.76/0.62    ~l1_struct_0(sK1) | r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK2))),
% 1.76/0.62    inference(resolution,[],[f151,f99])).
% 1.76/0.62  fof(f99,plain,(
% 1.76/0.62    r1_tsep_1(sK1,sK2)),
% 1.76/0.62    inference(subsumption_resolution,[],[f98,f78])).
% 1.76/0.62  fof(f78,plain,(
% 1.76/0.62    l1_struct_0(sK2)),
% 1.76/0.62    inference(resolution,[],[f72,f44])).
% 1.76/0.62  fof(f72,plain,(
% 1.76/0.62    l1_pre_topc(sK2)),
% 1.76/0.62    inference(resolution,[],[f71,f33])).
% 1.76/0.62  fof(f33,plain,(
% 1.76/0.62    m1_pre_topc(sK2,sK0)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f98,plain,(
% 1.76/0.62    ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2)),
% 1.76/0.62    inference(subsumption_resolution,[],[f97,f80])).
% 1.76/0.62  fof(f97,plain,(
% 1.76/0.62    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2)),
% 1.76/0.62    inference(duplicate_literal_removal,[],[f96])).
% 1.76/0.62  fof(f96,plain,(
% 1.76/0.62    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | r1_tsep_1(sK1,sK2) | r1_tsep_1(sK1,sK2)),
% 1.76/0.62    inference(resolution,[],[f61,f31])).
% 1.76/0.62  fof(f31,plain,(
% 1.76/0.62    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f61,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f30])).
% 1.76/0.62  fof(f30,plain,(
% 1.76/0.62    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.76/0.62    inference(flattening,[],[f29])).
% 1.76/0.62  fof(f29,plain,(
% 1.76/0.62    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f14])).
% 1.76/0.62  fof(f14,axiom,(
% 1.76/0.62    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 1.76/0.62  fof(f151,plain,(
% 1.76/0.62    ( ! [X1] : (~r1_tsep_1(X1,sK2) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X1),k2_struct_0(sK2))) )),
% 1.76/0.62    inference(forward_demodulation,[],[f148,f81])).
% 1.76/0.62  fof(f81,plain,(
% 1.76/0.62    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 1.76/0.62    inference(resolution,[],[f78,f41])).
% 1.76/0.62  fof(f148,plain,(
% 1.76/0.62    ( ! [X1] : (~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) | ~r1_tsep_1(X1,sK2)) )),
% 1.76/0.62    inference(resolution,[],[f43,f78])).
% 1.76/0.62  fof(f43,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f21])).
% 1.76/0.62  fof(f21,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f13])).
% 1.76/0.62  fof(f13,axiom,(
% 1.76/0.62    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 1.76/0.62  fof(f312,plain,(
% 1.76/0.62    k2_struct_0(sK1) = k4_xboole_0(k2_struct_0(sK1),k4_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))),
% 1.76/0.62    inference(resolution,[],[f232,f34])).
% 1.76/0.62  fof(f34,plain,(
% 1.76/0.62    m1_pre_topc(sK1,sK2)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f232,plain,(
% 1.76/0.62    ( ! [X1] : (~m1_pre_topc(X1,sK2) | k2_struct_0(X1) = k4_xboole_0(k2_struct_0(X1),k4_xboole_0(k2_struct_0(X1),k2_struct_0(sK2)))) )),
% 1.76/0.62    inference(resolution,[],[f181,f72])).
% 1.76/0.62  fof(f181,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X0) = k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1)))) )),
% 1.76/0.62    inference(subsumption_resolution,[],[f180,f55])).
% 1.76/0.62  fof(f180,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X0) = k4_xboole_0(k2_struct_0(X0),k4_xboole_0(k2_struct_0(X0),k2_struct_0(X1)))) )),
% 1.76/0.62    inference(resolution,[],[f54,f65])).
% 1.76/0.62  fof(f65,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.76/0.62    inference(definition_unfolding,[],[f59,f58])).
% 1.76/0.62  fof(f59,plain,(
% 1.76/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.76/0.62    inference(cnf_transformation,[],[f27])).
% 1.76/0.62  fof(f27,plain,(
% 1.76/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.76/0.62    inference(ennf_transformation,[],[f4])).
% 1.76/0.62  fof(f4,axiom,(
% 1.76/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.76/0.62  fof(f54,plain,(
% 1.76/0.62    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f23])).
% 1.76/0.62  fof(f23,plain,(
% 1.76/0.62    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.76/0.62    inference(ennf_transformation,[],[f9])).
% 1.76/0.62  fof(f9,axiom,(
% 1.76/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 1.76/0.62  fof(f89,plain,(
% 1.76/0.62    ~v1_xboole_0(k2_struct_0(sK1))),
% 1.76/0.62    inference(subsumption_resolution,[],[f88,f35])).
% 1.76/0.62  fof(f35,plain,(
% 1.76/0.62    ~v2_struct_0(sK1)),
% 1.76/0.62    inference(cnf_transformation,[],[f19])).
% 1.76/0.62  fof(f88,plain,(
% 1.76/0.62    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 1.76/0.62    inference(subsumption_resolution,[],[f87,f80])).
% 1.76/0.62  fof(f87,plain,(
% 1.76/0.62    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 1.76/0.62    inference(superposition,[],[f56,f82])).
% 1.76/0.62  fof(f56,plain,(
% 1.76/0.62    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.76/0.62    inference(cnf_transformation,[],[f26])).
% 1.76/0.62  fof(f26,plain,(
% 1.76/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.76/0.62    inference(flattening,[],[f25])).
% 1.76/0.62  fof(f25,plain,(
% 1.76/0.62    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.76/0.62    inference(ennf_transformation,[],[f12])).
% 1.76/0.62  fof(f12,axiom,(
% 1.76/0.62    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.76/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.76/0.62  % SZS output end Proof for theBenchmark
% 1.76/0.62  % (22649)------------------------------
% 1.76/0.62  % (22649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.62  % (22649)Termination reason: Refutation
% 1.76/0.62  
% 1.76/0.62  % (22649)Memory used [KB]: 6396
% 1.76/0.62  % (22649)Time elapsed: 0.114 s
% 1.76/0.62  % (22649)------------------------------
% 1.76/0.62  % (22649)------------------------------
% 1.76/0.62  % (22671)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.76/0.63  % (22668)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.76/0.63  % (22669)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.76/0.63  % (22642)Success in time 0.267 s
%------------------------------------------------------------------------------
