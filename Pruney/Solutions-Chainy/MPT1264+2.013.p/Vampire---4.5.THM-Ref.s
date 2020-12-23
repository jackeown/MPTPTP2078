%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:19 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 200 expanded)
%              Number of leaves         :    9 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  201 ( 869 expanded)
%              Number of equality atoms :   45 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f242])).

fof(f242,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | ~ spl3_8 ),
    inference(global_subsumption,[],[f69,f240])).

fof(f240,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f239,f67])).

fof(f67,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK1) = k3_xboole_0(X1,sK1) ),
    inference(resolution,[],[f36,f22])).

fof(f22,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f239,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f230,f237])).

fof(f237,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f236,f99])).

fof(f99,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f97,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f87,f40])).

fof(f40,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f87,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f83,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f83,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X2)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f80,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f27,f25])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f80,plain,(
    ! [X0] :
      ( v1_tops_1(X0,sK0)
      | ~ r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK1,X0)
      | v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f78,f23])).

fof(f23,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | v1_tops_1(X1,sK0) ) ),
    inference(resolution,[],[f28,f25])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_tops_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).

fof(f236,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f235,f43])).

fof(f43,plain,(
    sK2 = k3_xboole_0(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f19])).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f235,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0)))) = k2_pre_topc(sK0,k3_xboole_0(sK2,u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f225,f70])).

fof(f70,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(resolution,[],[f68,f37])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | k9_subset_1(X2,X3,X4) = k3_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f36,f34])).

fof(f225,plain,
    ( k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0)))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(resolution,[],[f222,f109])).

fof(f109,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl3_8
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f221,f19])).

fof(f221,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) ) ),
    inference(resolution,[],[f218,f20])).

fof(f20,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(subsumption_resolution,[],[f217,f25])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f29,f24])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).

fof(f230,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f224,f75])).

fof(f75,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f74,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f73,f23])).

fof(f224,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f222,f22])).

fof(f69,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f21,f67])).

fof(f21,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f114,plain,(
    spl3_8 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl3_8 ),
    inference(subsumption_resolution,[],[f112,f37])).

fof(f112,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_8 ),
    inference(resolution,[],[f110,f34])).

fof(f110,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.31  % Computer   : n001.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 13:45:59 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.17/0.43  % (18106)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.17/0.44  % (18098)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.45  % (18090)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.17/0.45  % (18102)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.17/0.45  % (18085)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.46  % (18087)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.17/0.46  % (18106)Refutation found. Thanks to Tanya!
% 0.17/0.46  % SZS status Theorem for theBenchmark
% 0.17/0.46  % SZS output start Proof for theBenchmark
% 0.17/0.46  fof(f253,plain,(
% 0.17/0.46    $false),
% 0.17/0.46    inference(avatar_sat_refutation,[],[f114,f242])).
% 0.17/0.46  fof(f242,plain,(
% 0.17/0.46    ~spl3_8),
% 0.17/0.46    inference(avatar_contradiction_clause,[],[f241])).
% 0.17/0.46  fof(f241,plain,(
% 0.17/0.46    $false | ~spl3_8),
% 0.17/0.46    inference(global_subsumption,[],[f69,f240])).
% 0.17/0.46  fof(f240,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) | ~spl3_8),
% 0.17/0.46    inference(forward_demodulation,[],[f239,f67])).
% 0.17/0.46  fof(f67,plain,(
% 0.17/0.46    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK1) = k3_xboole_0(X1,sK1)) )),
% 0.17/0.46    inference(resolution,[],[f36,f22])).
% 0.17/0.46  fof(f22,plain,(
% 0.17/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f11,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.17/0.46    inference(flattening,[],[f10])).
% 0.17/0.46  fof(f10,plain,(
% 0.17/0.46    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.17/0.46    inference(ennf_transformation,[],[f9])).
% 0.17/0.46  fof(f9,negated_conjecture,(
% 0.17/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.17/0.46    inference(negated_conjecture,[],[f8])).
% 0.17/0.46  fof(f8,conjecture,(
% 0.17/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 0.17/0.46  fof(f36,plain,(
% 0.17/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f18])).
% 0.17/0.46  fof(f18,plain,(
% 0.17/0.46    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.17/0.46    inference(ennf_transformation,[],[f3])).
% 0.17/0.46  fof(f3,axiom,(
% 0.17/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.17/0.46  fof(f239,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) | ~spl3_8),
% 0.17/0.46    inference(forward_demodulation,[],[f230,f237])).
% 0.17/0.46  fof(f237,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~spl3_8),
% 0.17/0.46    inference(forward_demodulation,[],[f236,f99])).
% 0.17/0.46  fof(f99,plain,(
% 0.17/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 0.17/0.46    inference(subsumption_resolution,[],[f97,f37])).
% 0.17/0.46  fof(f37,plain,(
% 0.17/0.46    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.17/0.46    inference(equality_resolution,[],[f32])).
% 0.17/0.46  fof(f32,plain,(
% 0.17/0.46    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.17/0.46    inference(cnf_transformation,[],[f1])).
% 0.17/0.46  fof(f1,axiom,(
% 0.17/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.17/0.46  fof(f97,plain,(
% 0.17/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.17/0.46    inference(resolution,[],[f87,f40])).
% 0.17/0.46  fof(f40,plain,(
% 0.17/0.46    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.17/0.46    inference(resolution,[],[f35,f22])).
% 0.17/0.46  fof(f35,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f4])).
% 0.17/0.46  fof(f4,axiom,(
% 0.17/0.46    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.17/0.46  fof(f87,plain,(
% 0.17/0.46    ( ! [X0] : (~r1_tarski(sK1,X0) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.17/0.46    inference(resolution,[],[f83,f34])).
% 0.17/0.46  fof(f34,plain,(
% 0.17/0.46    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f4])).
% 0.17/0.46  fof(f83,plain,(
% 0.17/0.46    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X2) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2)) )),
% 0.17/0.46    inference(duplicate_literal_removal,[],[f82])).
% 0.17/0.46  fof(f82,plain,(
% 0.17/0.46    ( ! [X2] : (~r1_tarski(sK1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.17/0.46    inference(resolution,[],[f80,f73])).
% 0.17/0.46  fof(f73,plain,(
% 0.17/0.46    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.17/0.46    inference(resolution,[],[f27,f25])).
% 0.17/0.46  fof(f25,plain,(
% 0.17/0.46    l1_pre_topc(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f27,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f12])).
% 0.17/0.46  fof(f12,plain,(
% 0.17/0.46    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.17/0.46    inference(ennf_transformation,[],[f5])).
% 0.17/0.46  fof(f5,axiom,(
% 0.17/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 0.17/0.46  fof(f80,plain,(
% 0.17/0.46    ( ! [X0] : (v1_tops_1(X0,sK0) | ~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.17/0.46    inference(subsumption_resolution,[],[f79,f22])).
% 0.17/0.46  fof(f79,plain,(
% 0.17/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | v1_tops_1(X0,sK0)) )),
% 0.17/0.46    inference(resolution,[],[f78,f23])).
% 0.17/0.46  fof(f23,plain,(
% 0.17/0.46    v1_tops_1(sK1,sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f78,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,X1) | v1_tops_1(X1,sK0)) )),
% 0.17/0.46    inference(resolution,[],[f28,f25])).
% 0.17/0.46  fof(f28,plain,(
% 0.17/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~r1_tarski(X1,X2) | v1_tops_1(X2,X0)) )),
% 0.17/0.46    inference(cnf_transformation,[],[f14])).
% 0.17/0.46  fof(f14,plain,(
% 0.17/0.46    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.17/0.46    inference(flattening,[],[f13])).
% 0.17/0.46  fof(f13,plain,(
% 0.17/0.46    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.17/0.46    inference(ennf_transformation,[],[f7])).
% 0.17/0.46  fof(f7,axiom,(
% 0.17/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_tops_1)).
% 0.17/0.46  fof(f236,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0)))) | ~spl3_8),
% 0.17/0.46    inference(forward_demodulation,[],[f235,f43])).
% 0.17/0.46  fof(f43,plain,(
% 0.17/0.46    sK2 = k3_xboole_0(sK2,u1_struct_0(sK0))),
% 0.17/0.46    inference(resolution,[],[f30,f39])).
% 0.17/0.46  fof(f39,plain,(
% 0.17/0.46    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.17/0.46    inference(resolution,[],[f35,f19])).
% 0.17/0.46  fof(f19,plain,(
% 0.17/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f30,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.17/0.46    inference(cnf_transformation,[],[f17])).
% 0.17/0.46  fof(f17,plain,(
% 0.17/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.17/0.46    inference(ennf_transformation,[],[f2])).
% 0.17/0.46  fof(f2,axiom,(
% 0.17/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.17/0.46  fof(f235,plain,(
% 0.17/0.46    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0)))) = k2_pre_topc(sK0,k3_xboole_0(sK2,u1_struct_0(sK0))) | ~spl3_8),
% 0.17/0.46    inference(forward_demodulation,[],[f225,f70])).
% 0.17/0.46  fof(f70,plain,(
% 0.17/0.46    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0)) )),
% 0.17/0.46    inference(resolution,[],[f68,f37])).
% 0.17/0.46  fof(f68,plain,(
% 0.17/0.46    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | k9_subset_1(X2,X3,X4) = k3_xboole_0(X3,X4)) )),
% 0.17/0.46    inference(resolution,[],[f36,f34])).
% 0.17/0.46  fof(f225,plain,(
% 0.17/0.46    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,u1_struct_0(sK0)))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))) | ~spl3_8),
% 0.17/0.46    inference(resolution,[],[f222,f109])).
% 0.17/0.46  fof(f109,plain,(
% 0.17/0.46    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.17/0.46    inference(avatar_component_clause,[],[f108])).
% 0.17/0.46  fof(f108,plain,(
% 0.17/0.46    spl3_8 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.17/0.46  fof(f222,plain,(
% 0.17/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))) )),
% 0.17/0.46    inference(subsumption_resolution,[],[f221,f19])).
% 0.17/0.46  fof(f221,plain,(
% 0.17/0.46    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))) )),
% 0.17/0.46    inference(resolution,[],[f218,f20])).
% 0.17/0.46  fof(f20,plain,(
% 0.17/0.46    v3_pre_topc(sK2,sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f218,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 0.17/0.46    inference(subsumption_resolution,[],[f217,f25])).
% 0.17/0.46  fof(f217,plain,(
% 0.17/0.46    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 0.17/0.46    inference(resolution,[],[f29,f24])).
% 0.17/0.46  fof(f24,plain,(
% 0.17/0.46    v2_pre_topc(sK0)),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f29,plain,(
% 0.17/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 0.17/0.46    inference(cnf_transformation,[],[f16])).
% 0.17/0.46  fof(f16,plain,(
% 0.17/0.46    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.17/0.46    inference(flattening,[],[f15])).
% 0.17/0.46  fof(f15,plain,(
% 0.17/0.46    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.17/0.46    inference(ennf_transformation,[],[f6])).
% 0.17/0.46  fof(f6,axiom,(
% 0.17/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.17/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 0.17/0.46  fof(f230,plain,(
% 0.17/0.46    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 0.17/0.46    inference(forward_demodulation,[],[f224,f75])).
% 0.17/0.46  fof(f75,plain,(
% 0.17/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.17/0.46    inference(subsumption_resolution,[],[f74,f22])).
% 0.17/0.46  fof(f74,plain,(
% 0.17/0.46    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.17/0.46    inference(resolution,[],[f73,f23])).
% 0.17/0.46  fof(f224,plain,(
% 0.17/0.46    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))),
% 0.17/0.46    inference(resolution,[],[f222,f22])).
% 0.17/0.46  fof(f69,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.17/0.46    inference(backward_demodulation,[],[f21,f67])).
% 0.17/0.46  fof(f21,plain,(
% 0.17/0.46    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.17/0.46    inference(cnf_transformation,[],[f11])).
% 0.17/0.46  fof(f114,plain,(
% 0.17/0.46    spl3_8),
% 0.17/0.46    inference(avatar_contradiction_clause,[],[f113])).
% 0.17/0.46  fof(f113,plain,(
% 0.17/0.46    $false | spl3_8),
% 0.17/0.46    inference(subsumption_resolution,[],[f112,f37])).
% 0.17/0.46  fof(f112,plain,(
% 0.17/0.46    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_8),
% 0.17/0.46    inference(resolution,[],[f110,f34])).
% 0.17/0.46  fof(f110,plain,(
% 0.17/0.46    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_8),
% 0.17/0.46    inference(avatar_component_clause,[],[f108])).
% 0.17/0.46  % SZS output end Proof for theBenchmark
% 0.17/0.46  % (18106)------------------------------
% 0.17/0.46  % (18106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.46  % (18106)Termination reason: Refutation
% 0.17/0.46  
% 0.17/0.46  % (18106)Memory used [KB]: 10746
% 0.17/0.46  % (18106)Time elapsed: 0.064 s
% 0.17/0.46  % (18106)------------------------------
% 0.17/0.46  % (18106)------------------------------
% 0.17/0.46  % (18095)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.17/0.46  % (18092)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.17/0.46  % (18100)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.17/0.46  % (18083)Success in time 0.136 s
%------------------------------------------------------------------------------
