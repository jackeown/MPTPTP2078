%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:32 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 380 expanded)
%              Number of leaves         :   25 ( 113 expanded)
%              Depth                    :   20
%              Number of atoms          :  448 (1666 expanded)
%              Number of equality atoms :   50 (  94 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1649,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1247,f1287,f1648])).

fof(f1648,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1647])).

fof(f1647,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1646,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ~ v2_tex_2(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ~ v2_tex_2(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tex_2(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f1646,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1645,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1645,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1640,f59])).

fof(f59,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1640,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f1635,f259])).

fof(f259,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f95,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f65,f63])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f95,plain,(
    ! [X0] :
      ( v2_tex_2(u1_struct_0(X0),X0)
      | ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_tdlat_3(X0)
      | u1_struct_0(X0) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_tdlat_3(X0) )
            & ( v1_tdlat_3(X0)
              | ~ v2_tex_2(X1,X0) ) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_tdlat_3(X0) )
          | u1_struct_0(X0) != X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).

fof(f1635,plain,
    ( ~ v2_tex_2(u1_struct_0(sK0),sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f1634,f104])).

fof(f1634,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X1,sK0) )
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f1633,f806])).

fof(f806,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f62,f804])).

fof(f804,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f162,plain,
    ( v1_xboole_0(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl2_2
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1633,plain,
    ( ! [X1] :
        ( v2_tex_2(k1_xboole_0,sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1632,f242])).

fof(f242,plain,(
    ! [X2,X3] : k1_xboole_0 = k9_subset_1(X2,X3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f241,f107])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f90,f99])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

% (17571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f241,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f237,f117])).

fof(f117,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f116,f107])).

fof(f116,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(resolution,[],[f93,f99])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f83,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f237,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(resolution,[],[f94,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f91,f82])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1632,plain,
    ( ! [X1] :
        ( v2_tex_2(k9_subset_1(k1_xboole_0,X1,k1_xboole_0),sK0)
        | ~ v2_tex_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f725,f804])).

fof(f725,plain,(
    ! [X1] :
      ( v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f724,f60])).

fof(f724,plain,(
    ! [X1] :
      ( v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f722,f61])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f722,plain,(
    ! [X1] :
      ( v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0)
      | ~ v2_tex_2(X1,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f72,f700])).

fof(f700,plain,(
    ! [X8] : k9_subset_1(u1_struct_0(sK0),X8,sK1) = k9_subset_1(sK1,X8,sK1) ),
    inference(backward_demodulation,[],[f240,f236])).

fof(f236,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f94,f104])).

fof(f240,plain,(
    ! [X8] : k9_subset_1(u1_struct_0(sK0),X8,sK1) = k4_xboole_0(X8,k4_xboole_0(X8,sK1)) ),
    inference(resolution,[],[f94,f61])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ( ~ v2_tex_2(X2,X0)
                & ~ v2_tex_2(X1,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f1287,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f1286,f160,f156])).

fof(f156,plain,
    ( spl2_1
  <=> v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1286,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f879,f137])).

fof(f137,plain,(
    l1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f136,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f136,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f135,f60])).

fof(f135,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f134,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f134,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f132,f60])).

fof(f132,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f61])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f879,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ v2_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f81,f143])).

fof(f143,plain,(
    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f141,f60])).

fof(f141,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f81,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f1247,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f1246])).

fof(f1246,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f1245,f57])).

fof(f1245,plain,
    ( v2_struct_0(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f1244,f60])).

fof(f1244,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f1243,f62])).

fof(f1243,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_1 ),
    inference(resolution,[],[f247,f134])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | v2_tex_2(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | spl2_1 ),
    inference(subsumption_resolution,[],[f246,f158])).

fof(f158,plain,
    ( ~ v2_struct_0(k1_pre_topc(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f156])).

fof(f246,plain,(
    ! [X0] :
      ( v2_tex_2(sK1,X0)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | v2_struct_0(k1_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f245,f174])).

fof(f174,plain,(
    v1_tdlat_3(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f173,f57])).

fof(f173,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f172,f59])).

fof(f172,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f60])).

fof(f169,plain,
    ( v1_tdlat_3(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f164,f134])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v1_tdlat_3(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f245,plain,(
    ! [X0] :
      ( v2_tex_2(sK1,X0)
      | ~ v1_tdlat_3(k1_pre_topc(sK0,sK1))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | v2_struct_0(k1_pre_topc(sK0,sK1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f101,f143])).

fof(f101,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f70,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:34:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (17557)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (17572)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (17564)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (17573)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (17553)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (17551)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (17554)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (17580)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (17574)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (17575)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (17566)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (17555)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (17552)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (17552)Refutation not found, incomplete strategy% (17552)------------------------------
% 0.21/0.55  % (17552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17552)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17552)Memory used [KB]: 1663
% 0.21/0.55  % (17552)Time elapsed: 0.132 s
% 0.21/0.55  % (17552)------------------------------
% 0.21/0.55  % (17552)------------------------------
% 0.21/0.55  % (17560)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (17569)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (17567)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (17578)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (17568)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (17561)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (17565)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (17576)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (17561)Refutation not found, incomplete strategy% (17561)------------------------------
% 0.21/0.55  % (17561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17561)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17561)Memory used [KB]: 10746
% 0.21/0.55  % (17561)Time elapsed: 0.140 s
% 0.21/0.55  % (17561)------------------------------
% 0.21/0.55  % (17561)------------------------------
% 0.21/0.55  % (17567)Refutation not found, incomplete strategy% (17567)------------------------------
% 0.21/0.55  % (17567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17567)Memory used [KB]: 10618
% 0.21/0.55  % (17567)Time elapsed: 0.149 s
% 0.21/0.55  % (17567)------------------------------
% 0.21/0.55  % (17567)------------------------------
% 0.21/0.55  % (17579)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (17559)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (17575)Refutation not found, incomplete strategy% (17575)------------------------------
% 0.21/0.56  % (17575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (17577)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (17569)Refutation not found, incomplete strategy% (17569)------------------------------
% 0.21/0.56  % (17569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17579)Refutation not found, incomplete strategy% (17579)------------------------------
% 0.21/0.56  % (17579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17578)Refutation not found, incomplete strategy% (17578)------------------------------
% 0.21/0.56  % (17578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17578)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17578)Memory used [KB]: 6268
% 0.21/0.56  % (17578)Time elapsed: 0.149 s
% 0.21/0.56  % (17578)------------------------------
% 0.21/0.56  % (17578)------------------------------
% 0.21/0.56  % (17570)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (17577)Refutation not found, incomplete strategy% (17577)------------------------------
% 0.21/0.56  % (17577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17569)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17569)Memory used [KB]: 1663
% 0.21/0.56  % (17569)Time elapsed: 0.149 s
% 0.21/0.56  % (17569)------------------------------
% 0.21/0.56  % (17569)------------------------------
% 0.21/0.56  % (17575)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17575)Memory used [KB]: 10618
% 0.21/0.56  % (17575)Time elapsed: 0.148 s
% 0.21/0.56  % (17575)------------------------------
% 0.21/0.56  % (17575)------------------------------
% 0.21/0.56  % (17580)Refutation not found, incomplete strategy% (17580)------------------------------
% 0.21/0.56  % (17580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17580)Memory used [KB]: 1663
% 0.21/0.56  % (17580)Time elapsed: 0.002 s
% 0.21/0.56  % (17580)------------------------------
% 0.21/0.56  % (17580)------------------------------
% 1.54/0.57  % (17576)Refutation not found, incomplete strategy% (17576)------------------------------
% 1.54/0.57  % (17576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (17576)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (17576)Memory used [KB]: 6268
% 1.54/0.57  % (17576)Time elapsed: 0.148 s
% 1.54/0.57  % (17576)------------------------------
% 1.54/0.57  % (17576)------------------------------
% 1.54/0.57  % (17570)Refutation not found, incomplete strategy% (17570)------------------------------
% 1.54/0.57  % (17570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (17579)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (17579)Memory used [KB]: 10746
% 1.54/0.57  % (17579)Time elapsed: 0.149 s
% 1.54/0.57  % (17579)------------------------------
% 1.54/0.57  % (17579)------------------------------
% 1.54/0.57  % (17577)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (17577)Memory used [KB]: 6268
% 1.54/0.57  % (17577)Time elapsed: 0.148 s
% 1.54/0.57  % (17577)------------------------------
% 1.54/0.57  % (17577)------------------------------
% 1.54/0.57  % (17570)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (17570)Memory used [KB]: 1663
% 1.54/0.57  % (17570)Time elapsed: 0.158 s
% 1.54/0.57  % (17570)------------------------------
% 1.54/0.57  % (17570)------------------------------
% 1.54/0.57  % (17556)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.54/0.57  % (17558)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.54/0.58  % (17563)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.54/0.58  % (17556)Refutation not found, incomplete strategy% (17556)------------------------------
% 1.54/0.58  % (17556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (17557)Refutation found. Thanks to Tanya!
% 1.54/0.58  % SZS status Theorem for theBenchmark
% 1.54/0.58  % SZS output start Proof for theBenchmark
% 1.54/0.58  fof(f1649,plain,(
% 1.54/0.58    $false),
% 1.54/0.58    inference(avatar_sat_refutation,[],[f1247,f1287,f1648])).
% 1.54/0.58  fof(f1648,plain,(
% 1.54/0.58    ~spl2_2),
% 1.54/0.58    inference(avatar_contradiction_clause,[],[f1647])).
% 1.54/0.58  fof(f1647,plain,(
% 1.54/0.58    $false | ~spl2_2),
% 1.54/0.58    inference(subsumption_resolution,[],[f1646,f57])).
% 1.54/0.58  fof(f57,plain,(
% 1.54/0.58    ~v2_struct_0(sK0)),
% 1.54/0.58    inference(cnf_transformation,[],[f51])).
% 1.54/0.58  fof(f51,plain,(
% 1.54/0.58    (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.54/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f50,f49])).
% 1.54/0.58  fof(f49,plain,(
% 1.54/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f50,plain,(
% 1.54/0.58    ? [X1] : (~v2_tex_2(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v2_tex_2(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.54/0.58    introduced(choice_axiom,[])).
% 1.54/0.58  fof(f25,plain,(
% 1.54/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.54/0.58    inference(flattening,[],[f24])).
% 1.54/0.58  fof(f24,plain,(
% 1.54/0.58    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.54/0.58    inference(ennf_transformation,[],[f23])).
% 1.54/0.58  fof(f23,negated_conjecture,(
% 1.54/0.58    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.54/0.58    inference(negated_conjecture,[],[f22])).
% 1.54/0.58  fof(f22,conjecture,(
% 1.54/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 1.54/0.58  fof(f1646,plain,(
% 1.54/0.58    v2_struct_0(sK0) | ~spl2_2),
% 1.54/0.58    inference(subsumption_resolution,[],[f1645,f60])).
% 1.54/0.58  fof(f60,plain,(
% 1.54/0.58    l1_pre_topc(sK0)),
% 1.54/0.58    inference(cnf_transformation,[],[f51])).
% 1.54/0.58  fof(f1645,plain,(
% 1.54/0.58    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_2),
% 1.54/0.58    inference(subsumption_resolution,[],[f1640,f59])).
% 1.54/0.58  fof(f59,plain,(
% 1.54/0.58    v1_tdlat_3(sK0)),
% 1.54/0.58    inference(cnf_transformation,[],[f51])).
% 1.54/0.58  fof(f1640,plain,(
% 1.54/0.58    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_2),
% 1.54/0.58    inference(resolution,[],[f1635,f259])).
% 1.54/0.58  fof(f259,plain,(
% 1.54/0.58    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.54/0.58    inference(subsumption_resolution,[],[f95,f104])).
% 1.54/0.58  fof(f104,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(forward_demodulation,[],[f65,f63])).
% 1.54/0.58  fof(f63,plain,(
% 1.54/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.54/0.58    inference(cnf_transformation,[],[f6])).
% 1.54/0.58  fof(f6,axiom,(
% 1.54/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.54/0.58  fof(f65,plain,(
% 1.54/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.54/0.58    inference(cnf_transformation,[],[f7])).
% 1.54/0.58  fof(f7,axiom,(
% 1.54/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.54/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.70/0.58  fof(f95,plain,(
% 1.70/0.58    ( ! [X0] : (v2_tex_2(u1_struct_0(X0),X0) | ~v1_tdlat_3(X0) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.58    inference(equality_resolution,[],[f78])).
% 1.70/0.58  fof(f78,plain,(
% 1.70/0.58    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_tdlat_3(X0) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.58    inference(cnf_transformation,[],[f52])).
% 1.70/0.58  fof(f52,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_tdlat_3(X0)) & (v1_tdlat_3(X0) | ~v2_tex_2(X1,X0))) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.58    inference(nnf_transformation,[],[f38])).
% 1.70/0.58  fof(f38,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.58    inference(flattening,[],[f37])).
% 1.70/0.58  fof(f37,plain,(
% 1.70/0.58    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)) | u1_struct_0(X0) != X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.58    inference(ennf_transformation,[],[f20])).
% 1.70/0.58  fof(f20,axiom,(
% 1.70/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X0) = X1 => (v2_tex_2(X1,X0) <=> v1_tdlat_3(X0)))))),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tex_2)).
% 1.70/0.58  fof(f1635,plain,(
% 1.70/0.58    ~v2_tex_2(u1_struct_0(sK0),sK0) | ~spl2_2),
% 1.70/0.58    inference(resolution,[],[f1634,f104])).
% 1.70/0.58  fof(f1634,plain,(
% 1.70/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0)) ) | ~spl2_2),
% 1.70/0.58    inference(subsumption_resolution,[],[f1633,f806])).
% 1.70/0.58  fof(f806,plain,(
% 1.70/0.58    ~v2_tex_2(k1_xboole_0,sK0) | ~spl2_2),
% 1.70/0.58    inference(backward_demodulation,[],[f62,f804])).
% 1.70/0.58  fof(f804,plain,(
% 1.70/0.58    k1_xboole_0 = sK1 | ~spl2_2),
% 1.70/0.58    inference(resolution,[],[f162,f66])).
% 1.70/0.58  fof(f66,plain,(
% 1.70/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.70/0.58    inference(cnf_transformation,[],[f26])).
% 1.70/0.58  fof(f26,plain,(
% 1.70/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.70/0.58    inference(ennf_transformation,[],[f1])).
% 1.70/0.58  fof(f1,axiom,(
% 1.70/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.70/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.70/0.58  fof(f162,plain,(
% 1.70/0.58    v1_xboole_0(sK1) | ~spl2_2),
% 1.70/0.58    inference(avatar_component_clause,[],[f160])).
% 1.70/0.58  fof(f160,plain,(
% 1.70/0.58    spl2_2 <=> v1_xboole_0(sK1)),
% 1.70/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.70/0.58  fof(f62,plain,(
% 1.70/0.58    ~v2_tex_2(sK1,sK0)),
% 1.70/0.58    inference(cnf_transformation,[],[f51])).
% 1.70/0.58  fof(f1633,plain,(
% 1.70/0.58    ( ! [X1] : (v2_tex_2(k1_xboole_0,sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 1.70/0.58    inference(forward_demodulation,[],[f1632,f242])).
% 1.70/0.58  fof(f242,plain,(
% 1.70/0.58    ( ! [X2,X3] : (k1_xboole_0 = k9_subset_1(X2,X3,k1_xboole_0)) )),
% 1.70/0.58    inference(forward_demodulation,[],[f241,f107])).
% 1.70/0.58  fof(f107,plain,(
% 1.70/0.58    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.70/0.58    inference(resolution,[],[f90,f99])).
% 1.70/0.59  fof(f99,plain,(
% 1.70/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.70/0.59    inference(equality_resolution,[],[f87])).
% 1.70/0.59  fof(f87,plain,(
% 1.70/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.70/0.59    inference(cnf_transformation,[],[f55])).
% 1.70/0.59  fof(f55,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(flattening,[],[f54])).
% 1.70/0.59  fof(f54,plain,(
% 1.70/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.70/0.59    inference(nnf_transformation,[],[f2])).
% 1.70/0.59  fof(f2,axiom,(
% 1.70/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.70/0.59  % (17571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.70/0.59  fof(f90,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f56])).
% 1.70/0.59  fof(f56,plain,(
% 1.70/0.59    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.70/0.59    inference(nnf_transformation,[],[f3])).
% 1.70/0.59  fof(f3,axiom,(
% 1.70/0.59    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.70/0.59  fof(f241,plain,(
% 1.70/0.59    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,X3)) )),
% 1.70/0.59    inference(forward_demodulation,[],[f237,f117])).
% 1.70/0.59  fof(f117,plain,(
% 1.70/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.59    inference(forward_demodulation,[],[f116,f107])).
% 1.70/0.59  fof(f116,plain,(
% 1.70/0.59    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.70/0.59    inference(resolution,[],[f93,f99])).
% 1.70/0.59  fof(f93,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.70/0.59    inference(definition_unfolding,[],[f83,f82])).
% 1.70/0.59  fof(f82,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f5])).
% 1.70/0.59  fof(f5,axiom,(
% 1.70/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.70/0.59  fof(f83,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f43])).
% 1.70/0.59  fof(f43,plain,(
% 1.70/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.70/0.59    inference(ennf_transformation,[],[f4])).
% 1.70/0.59  fof(f4,axiom,(
% 1.70/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.70/0.59  fof(f237,plain,(
% 1.70/0.59    ( ! [X2,X3] : (k9_subset_1(X2,X3,k1_xboole_0) = k4_xboole_0(X3,k4_xboole_0(X3,k1_xboole_0))) )),
% 1.70/0.59    inference(resolution,[],[f94,f64])).
% 1.70/0.59  fof(f64,plain,(
% 1.70/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f9])).
% 1.70/0.59  fof(f9,axiom,(
% 1.70/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.70/0.59  fof(f94,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.70/0.59    inference(definition_unfolding,[],[f91,f82])).
% 1.70/0.59  fof(f91,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.70/0.59    inference(cnf_transformation,[],[f46])).
% 1.70/0.59  fof(f46,plain,(
% 1.70/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f8])).
% 1.70/0.59  fof(f8,axiom,(
% 1.70/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.70/0.59  fof(f1632,plain,(
% 1.70/0.59    ( ! [X1] : (v2_tex_2(k9_subset_1(k1_xboole_0,X1,k1_xboole_0),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 1.70/0.59    inference(forward_demodulation,[],[f725,f804])).
% 1.70/0.59  fof(f725,plain,(
% 1.70/0.59    ( ! [X1] : (v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f724,f60])).
% 1.70/0.59  fof(f724,plain,(
% 1.70/0.59    ( ! [X1] : (v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f722,f61])).
% 1.70/0.59  fof(f61,plain,(
% 1.70/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.70/0.59    inference(cnf_transformation,[],[f51])).
% 1.70/0.59  fof(f722,plain,(
% 1.70/0.59    ( ! [X1] : (v2_tex_2(k9_subset_1(sK1,X1,sK1),sK0) | ~v2_tex_2(X1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.70/0.59    inference(superposition,[],[f72,f700])).
% 1.70/0.59  fof(f700,plain,(
% 1.70/0.59    ( ! [X8] : (k9_subset_1(u1_struct_0(sK0),X8,sK1) = k9_subset_1(sK1,X8,sK1)) )),
% 1.70/0.59    inference(backward_demodulation,[],[f240,f236])).
% 1.70/0.59  fof(f236,plain,(
% 1.70/0.59    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.70/0.59    inference(resolution,[],[f94,f104])).
% 1.70/0.59  fof(f240,plain,(
% 1.70/0.59    ( ! [X8] : (k9_subset_1(u1_struct_0(sK0),X8,sK1) = k4_xboole_0(X8,k4_xboole_0(X8,sK1))) )),
% 1.70/0.59    inference(resolution,[],[f94,f61])).
% 1.70/0.59  fof(f72,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f34])).
% 1.70/0.59  fof(f34,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(flattening,[],[f33])).
% 1.70/0.59  fof(f33,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v2_tex_2(X2,X0) & ~v2_tex_2(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f21])).
% 1.70/0.59  fof(f21,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 1.70/0.59  fof(f1287,plain,(
% 1.70/0.59    ~spl2_1 | spl2_2),
% 1.70/0.59    inference(avatar_split_clause,[],[f1286,f160,f156])).
% 1.70/0.59  fof(f156,plain,(
% 1.70/0.59    spl2_1 <=> v2_struct_0(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.70/0.59  fof(f1286,plain,(
% 1.70/0.59    v1_xboole_0(sK1) | ~v2_struct_0(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(subsumption_resolution,[],[f879,f137])).
% 1.70/0.59  fof(f137,plain,(
% 1.70/0.59    l1_struct_0(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(resolution,[],[f136,f67])).
% 1.70/0.59  fof(f67,plain,(
% 1.70/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f27])).
% 1.70/0.59  fof(f27,plain,(
% 1.70/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f12])).
% 1.70/0.59  fof(f12,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.70/0.59  fof(f136,plain,(
% 1.70/0.59    l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(subsumption_resolution,[],[f135,f60])).
% 1.70/0.59  fof(f135,plain,(
% 1.70/0.59    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.70/0.59    inference(resolution,[],[f134,f69])).
% 1.70/0.59  fof(f69,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f30])).
% 1.70/0.59  fof(f30,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f13])).
% 1.70/0.59  fof(f13,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.70/0.59  fof(f134,plain,(
% 1.70/0.59    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 1.70/0.59    inference(subsumption_resolution,[],[f132,f60])).
% 1.70/0.59  fof(f132,plain,(
% 1.70/0.59    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~l1_pre_topc(sK0)),
% 1.70/0.59    inference(resolution,[],[f85,f61])).
% 1.70/0.59  fof(f85,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f45])).
% 1.70/0.59  fof(f45,plain,(
% 1.70/0.59    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(flattening,[],[f44])).
% 1.70/0.59  fof(f44,plain,(
% 1.70/0.59    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f11])).
% 1.70/0.59  fof(f11,axiom,(
% 1.70/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.70/0.59  fof(f879,plain,(
% 1.70/0.59    v1_xboole_0(sK1) | ~l1_struct_0(k1_pre_topc(sK0,sK1)) | ~v2_struct_0(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(superposition,[],[f81,f143])).
% 1.70/0.59  fof(f143,plain,(
% 1.70/0.59    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(subsumption_resolution,[],[f141,f60])).
% 1.70/0.59  fof(f141,plain,(
% 1.70/0.59    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.70/0.59    inference(resolution,[],[f71,f61])).
% 1.70/0.59  fof(f71,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f32])).
% 1.70/0.59  fof(f32,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f15])).
% 1.70/0.59  fof(f15,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.70/0.59  fof(f81,plain,(
% 1.70/0.59    ( ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f42])).
% 1.70/0.59  fof(f42,plain,(
% 1.70/0.59    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f41])).
% 1.70/0.59  fof(f41,plain,(
% 1.70/0.59    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f14])).
% 1.70/0.59  fof(f14,axiom,(
% 1.70/0.59    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 1.70/0.59  fof(f1247,plain,(
% 1.70/0.59    spl2_1),
% 1.70/0.59    inference(avatar_contradiction_clause,[],[f1246])).
% 1.70/0.59  fof(f1246,plain,(
% 1.70/0.59    $false | spl2_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f1245,f57])).
% 1.70/0.59  fof(f1245,plain,(
% 1.70/0.59    v2_struct_0(sK0) | spl2_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f1244,f60])).
% 1.70/0.59  fof(f1244,plain,(
% 1.70/0.59    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl2_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f1243,f62])).
% 1.70/0.59  fof(f1243,plain,(
% 1.70/0.59    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl2_1),
% 1.70/0.59    inference(resolution,[],[f247,f134])).
% 1.70/0.59  fof(f247,plain,(
% 1.70/0.59    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | v2_tex_2(sK1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) ) | spl2_1),
% 1.70/0.59    inference(subsumption_resolution,[],[f246,f158])).
% 1.70/0.59  fof(f158,plain,(
% 1.70/0.59    ~v2_struct_0(k1_pre_topc(sK0,sK1)) | spl2_1),
% 1.70/0.59    inference(avatar_component_clause,[],[f156])).
% 1.70/0.59  fof(f246,plain,(
% 1.70/0.59    ( ! [X0] : (v2_tex_2(sK1,X0) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f245,f174])).
% 1.70/0.59  fof(f174,plain,(
% 1.70/0.59    v1_tdlat_3(k1_pre_topc(sK0,sK1))),
% 1.70/0.59    inference(subsumption_resolution,[],[f173,f57])).
% 1.70/0.59  fof(f173,plain,(
% 1.70/0.59    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | v2_struct_0(sK0)),
% 1.70/0.59    inference(subsumption_resolution,[],[f172,f59])).
% 1.70/0.59  fof(f172,plain,(
% 1.70/0.59    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~v1_tdlat_3(sK0) | v2_struct_0(sK0)),
% 1.70/0.59    inference(subsumption_resolution,[],[f169,f60])).
% 1.70/0.59  fof(f169,plain,(
% 1.70/0.59    v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~v1_tdlat_3(sK0) | v2_struct_0(sK0)),
% 1.70/0.59    inference(resolution,[],[f164,f134])).
% 1.70/0.59  fof(f164,plain,(
% 1.70/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v1_tdlat_3(X1) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(subsumption_resolution,[],[f76,f68])).
% 1.70/0.59  fof(f68,plain,(
% 1.70/0.59    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f29])).
% 1.70/0.59  fof(f29,plain,(
% 1.70/0.59    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(flattening,[],[f28])).
% 1.70/0.59  fof(f28,plain,(
% 1.70/0.59    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f17])).
% 1.70/0.59  fof(f17,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 1.70/0.59  fof(f76,plain,(
% 1.70/0.59    ( ! [X0,X1] : (v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f36])).
% 1.70/0.59  fof(f36,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f35])).
% 1.70/0.59  fof(f35,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f18])).
% 1.70/0.59  fof(f18,axiom,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 1.70/0.59  fof(f245,plain,(
% 1.70/0.59    ( ! [X0] : (v2_tex_2(sK1,X0) | ~v1_tdlat_3(k1_pre_topc(sK0,sK1)) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | v2_struct_0(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(superposition,[],[f101,f143])).
% 1.70/0.59  fof(f101,plain,(
% 1.70/0.59    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(global_subsumption,[],[f70,f97])).
% 1.70/0.59  fof(f97,plain,(
% 1.70/0.59    ( ! [X0,X1] : (v2_tex_2(u1_struct_0(X1),X0) | ~v1_tdlat_3(X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(equality_resolution,[],[f80])).
% 1.70/0.59  fof(f80,plain,(
% 1.70/0.59    ( ! [X2,X0,X1] : (v2_tex_2(X2,X0) | ~v1_tdlat_3(X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f53])).
% 1.70/0.59  fof(f53,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) | ~v1_tdlat_3(X1)) & (v1_tdlat_3(X1) | ~v2_tex_2(X2,X0))) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(nnf_transformation,[],[f40])).
% 1.70/0.59  fof(f40,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.70/0.59    inference(flattening,[],[f39])).
% 1.70/0.59  fof(f39,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.70/0.59    inference(ennf_transformation,[],[f19])).
% 1.70/0.59  fof(f19,axiom,(
% 1.70/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).
% 1.70/0.59  fof(f70,plain,(
% 1.70/0.59    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.70/0.59    inference(cnf_transformation,[],[f31])).
% 1.70/0.59  fof(f31,plain,(
% 1.70/0.59    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.70/0.59    inference(ennf_transformation,[],[f16])).
% 1.70/0.59  fof(f16,axiom,(
% 1.70/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.70/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 1.70/0.59  % SZS output end Proof for theBenchmark
% 1.70/0.59  % (17557)------------------------------
% 1.70/0.59  % (17557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (17557)Termination reason: Refutation
% 1.70/0.59  
% 1.70/0.59  % (17557)Memory used [KB]: 11385
% 1.70/0.59  % (17557)Time elapsed: 0.176 s
% 1.70/0.59  % (17557)------------------------------
% 1.70/0.59  % (17557)------------------------------
% 1.70/0.59  % (17556)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (17556)Memory used [KB]: 1791
% 1.70/0.59  % (17556)Time elapsed: 0.145 s
% 1.70/0.59  % (17556)------------------------------
% 1.70/0.59  % (17556)------------------------------
% 1.70/0.59  % (17563)Refutation not found, incomplete strategy% (17563)------------------------------
% 1.70/0.59  % (17563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.59  % (17563)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.59  
% 1.70/0.59  % (17563)Memory used [KB]: 10618
% 1.70/0.59  % (17563)Time elapsed: 0.153 s
% 1.70/0.59  % (17563)------------------------------
% 1.70/0.59  % (17563)------------------------------
% 1.70/0.59  % (17550)Success in time 0.22 s
%------------------------------------------------------------------------------
