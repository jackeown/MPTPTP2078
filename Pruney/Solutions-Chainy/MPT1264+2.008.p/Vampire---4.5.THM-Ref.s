%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:18 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 610 expanded)
%              Number of leaves         :   15 ( 209 expanded)
%              Depth                    :   20
%              Number of atoms          :  291 (3076 expanded)
%              Number of equality atoms :   79 ( 601 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f297,f318])).

fof(f318,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f316,f195])).

fof(f195,plain,(
    r1_tarski(sK2,k2_struct_0(sK0)) ),
    inference(superposition,[],[f59,f62])).

fof(f62,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f57,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    & v3_pre_topc(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
                & v3_pre_topc(X2,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
              & v3_pre_topc(X2,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & v1_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1))
            & v3_pre_topc(X2,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v1_tops_1(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
          & v3_pre_topc(X2,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1))
        & v3_pre_topc(X2,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
      & v3_pre_topc(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f59,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f48,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f316,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK0))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f315,f55])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f315,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_struct_0(sK0))
    | spl4_11 ),
    inference(subsumption_resolution,[],[f308,f183])).

fof(f183,plain,
    ( sK2 != k3_xboole_0(k2_struct_0(sK0),sK2)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl4_11
  <=> sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f308,plain,
    ( sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)
    | ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_struct_0(sK0))
    | spl4_11 ),
    inference(resolution,[],[f302,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
     => ( ~ r1_tarski(sK3(X0,X1,X2),X0)
        & r1_tarski(sK3(X0,X1,X2),X2)
        & r1_tarski(sK3(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f302,plain,
    ( r1_tarski(sK3(sK2,k2_struct_0(sK0),sK2),sK2)
    | spl4_11 ),
    inference(forward_demodulation,[],[f301,f62])).

fof(f301,plain,
    ( r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2)
    | spl4_11 ),
    inference(subsumption_resolution,[],[f194,f183])).

fof(f194,plain,
    ( sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)
    | r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2) ),
    inference(forward_demodulation,[],[f192,f62])).

fof(f192,plain,
    ( sK2 = k3_xboole_0(u1_struct_0(sK0),sK2)
    | r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2) ),
    inference(resolution,[],[f90,f59])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X0) = X0
      | r1_tarski(sK3(X0,X1,X0),X0) ) ),
    inference(resolution,[],[f53,f55])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X1,X2) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f297,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f295,f204])).

fof(f204,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f203,f142])).

fof(f142,plain,(
    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f70,f66])).

fof(f66,plain,(
    ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(k2_struct_0(sK0),X1,sK2) ),
    inference(forward_demodulation,[],[f64,f62])).

fof(f64,plain,(
    ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),X1,sK2) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0) ),
    inference(forward_demodulation,[],[f69,f65])).

fof(f65,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(resolution,[],[f50,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0) ),
    inference(forward_demodulation,[],[f67,f62])).

fof(f67,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f203,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(forward_demodulation,[],[f197,f65])).

fof(f197,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(superposition,[],[f39,f62])).

fof(f39,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f295,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f294,f184])).

fof(f184,plain,
    ( sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f182])).

fof(f294,plain,(
    k2_pre_topc(sK0,k3_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f293,f142])).

fof(f293,plain,(
    k2_pre_topc(sK0,k3_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(forward_demodulation,[],[f292,f72])).

fof(f72,plain,(
    ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X1) ),
    inference(forward_demodulation,[],[f71,f66])).

fof(f71,plain,(
    ! [X1] : k9_subset_1(k2_struct_0(sK0),X1,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X1) ),
    inference(forward_demodulation,[],[f68,f62])).

fof(f68,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1) ),
    inference(resolution,[],[f51,f37])).

fof(f292,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f286,f38])).

fof(f38,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f286,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f198,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k3_xboole_0(X0,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f97,f62])).

fof(f97,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k3_xboole_0(X0,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f96,f76])).

fof(f76,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f75,f34])).

fof(f75,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f73,f36])).

fof(f36,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f73,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f96,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k3_xboole_0(X0,sK1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f95,f65])).

fof(f95,plain,(
    ! [X0] :
      ( k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,sK1))
      | ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f94,f62])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f93,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f34])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).

fof(f198,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f37,f62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 13:29:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.52  % (7617)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.52  % (7609)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.53  % (7610)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.53  % (7602)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.53  % (7609)Refutation found. Thanks to Tanya!
% 0.19/0.53  % SZS status Theorem for theBenchmark
% 0.19/0.54  % (7610)Refutation not found, incomplete strategy% (7610)------------------------------
% 0.19/0.54  % (7610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (7610)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (7610)Memory used [KB]: 10618
% 0.19/0.54  % (7610)Time elapsed: 0.107 s
% 0.19/0.54  % (7610)------------------------------
% 0.19/0.54  % (7610)------------------------------
% 0.19/0.54  % SZS output start Proof for theBenchmark
% 0.19/0.54  fof(f319,plain,(
% 0.19/0.54    $false),
% 0.19/0.54    inference(avatar_sat_refutation,[],[f297,f318])).
% 0.19/0.54  fof(f318,plain,(
% 0.19/0.54    spl4_11),
% 0.19/0.54    inference(avatar_contradiction_clause,[],[f317])).
% 0.19/0.54  fof(f317,plain,(
% 0.19/0.54    $false | spl4_11),
% 0.19/0.54    inference(subsumption_resolution,[],[f316,f195])).
% 0.19/0.54  fof(f195,plain,(
% 0.19/0.54    r1_tarski(sK2,k2_struct_0(sK0))),
% 0.19/0.54    inference(superposition,[],[f59,f62])).
% 0.19/0.54  fof(f62,plain,(
% 0.19/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.19/0.54    inference(resolution,[],[f57,f40])).
% 0.19/0.54  fof(f40,plain,(
% 0.19/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f14])).
% 0.19/0.54  fof(f14,plain,(
% 0.19/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f6])).
% 0.19/0.54  fof(f6,axiom,(
% 0.19/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.54  fof(f57,plain,(
% 0.19/0.54    l1_struct_0(sK0)),
% 0.19/0.54    inference(resolution,[],[f41,f34])).
% 0.19/0.54  fof(f34,plain,(
% 0.19/0.54    l1_pre_topc(sK0)),
% 0.19/0.54    inference(cnf_transformation,[],[f26])).
% 0.19/0.54  fof(f26,plain,(
% 0.19/0.54    ((k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.19/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25,f24,f23])).
% 0.19/0.54  fof(f23,plain,(
% 0.19/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f24,plain,(
% 0.19/0.54    ? [X1] : (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,X1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & v1_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f25,plain,(
% 0.19/0.54    ? [X2] : (k2_pre_topc(sK0,X2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X2,sK1)) & v3_pre_topc(X2,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) & v3_pre_topc(sK2,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.54    introduced(choice_axiom,[])).
% 0.19/0.54  fof(f13,plain,(
% 0.19/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.19/0.54    inference(flattening,[],[f12])).
% 0.19/0.54  fof(f12,plain,(
% 0.19/0.54    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.19/0.54    inference(ennf_transformation,[],[f11])).
% 0.19/0.54  fof(f11,negated_conjecture,(
% 0.19/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.19/0.54    inference(negated_conjecture,[],[f10])).
% 0.19/0.54  fof(f10,conjecture,(
% 0.19/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.19/0.54  fof(f41,plain,(
% 0.19/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f15])).
% 0.19/0.54  fof(f15,plain,(
% 0.19/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.54    inference(ennf_transformation,[],[f7])).
% 0.19/0.54  fof(f7,axiom,(
% 0.19/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.54  fof(f59,plain,(
% 0.19/0.54    r1_tarski(sK2,u1_struct_0(sK0))),
% 0.19/0.54    inference(resolution,[],[f48,f37])).
% 0.19/0.54  fof(f37,plain,(
% 0.19/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.54    inference(cnf_transformation,[],[f26])).
% 0.19/0.54  fof(f48,plain,(
% 0.19/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.54    inference(cnf_transformation,[],[f30])).
% 0.19/0.54  fof(f30,plain,(
% 0.19/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.54    inference(nnf_transformation,[],[f5])).
% 0.19/0.54  fof(f5,axiom,(
% 0.19/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.54  fof(f316,plain,(
% 0.19/0.54    ~r1_tarski(sK2,k2_struct_0(sK0)) | spl4_11),
% 0.19/0.54    inference(subsumption_resolution,[],[f315,f55])).
% 0.19/0.54  fof(f55,plain,(
% 0.19/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.19/0.54    inference(equality_resolution,[],[f46])).
% 0.19/0.54  fof(f46,plain,(
% 0.19/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.19/0.54    inference(cnf_transformation,[],[f29])).
% 0.19/0.54  fof(f29,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(flattening,[],[f28])).
% 0.19/0.54  fof(f28,plain,(
% 0.19/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.19/0.54    inference(nnf_transformation,[],[f1])).
% 0.19/0.54  fof(f1,axiom,(
% 0.19/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.54  fof(f315,plain,(
% 0.19/0.54    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_struct_0(sK0)) | spl4_11),
% 0.19/0.54    inference(subsumption_resolution,[],[f308,f183])).
% 0.19/0.54  fof(f183,plain,(
% 0.19/0.54    sK2 != k3_xboole_0(k2_struct_0(sK0),sK2) | spl4_11),
% 0.19/0.54    inference(avatar_component_clause,[],[f182])).
% 0.19/0.54  fof(f182,plain,(
% 0.19/0.54    spl4_11 <=> sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)),
% 0.19/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.54  fof(f308,plain,(
% 0.19/0.54    sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) | ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_struct_0(sK0)) | spl4_11),
% 0.19/0.54    inference(resolution,[],[f302,f54])).
% 0.19/0.55  fof(f54,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f32])).
% 0.19/0.55  fof(f32,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f31])).
% 0.19/0.55  fof(f31,plain,(
% 0.19/0.55    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) => (~r1_tarski(sK3(X0,X1,X2),X0) & r1_tarski(sK3(X0,X1,X2),X2) & r1_tarski(sK3(X0,X1,X2),X1)))),
% 0.19/0.55    introduced(choice_axiom,[])).
% 0.19/0.55  fof(f22,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.19/0.55    inference(flattening,[],[f21])).
% 0.19/0.55  fof(f21,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.19/0.55    inference(ennf_transformation,[],[f2])).
% 0.19/0.55  fof(f2,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).
% 0.19/0.55  fof(f302,plain,(
% 0.19/0.55    r1_tarski(sK3(sK2,k2_struct_0(sK0),sK2),sK2) | spl4_11),
% 0.19/0.55    inference(forward_demodulation,[],[f301,f62])).
% 0.19/0.55  fof(f301,plain,(
% 0.19/0.55    r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2) | spl4_11),
% 0.19/0.55    inference(subsumption_resolution,[],[f194,f183])).
% 0.19/0.55  fof(f194,plain,(
% 0.19/0.55    sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) | r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2)),
% 0.19/0.55    inference(forward_demodulation,[],[f192,f62])).
% 0.19/0.55  fof(f192,plain,(
% 0.19/0.55    sK2 = k3_xboole_0(u1_struct_0(sK0),sK2) | r1_tarski(sK3(sK2,u1_struct_0(sK0),sK2),sK2)),
% 0.19/0.55    inference(resolution,[],[f90,f59])).
% 0.19/0.55  fof(f90,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X1,X0) = X0 | r1_tarski(sK3(X0,X1,X0),X0)) )),
% 0.19/0.55    inference(resolution,[],[f53,f55])).
% 0.19/0.55  fof(f53,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | r1_tarski(sK3(X0,X1,X2),X2) | k3_xboole_0(X1,X2) = X0 | ~r1_tarski(X0,X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f32])).
% 0.19/0.55  fof(f297,plain,(
% 0.19/0.55    ~spl4_11),
% 0.19/0.55    inference(avatar_contradiction_clause,[],[f296])).
% 0.19/0.55  fof(f296,plain,(
% 0.19/0.55    $false | ~spl4_11),
% 0.19/0.55    inference(subsumption_resolution,[],[f295,f204])).
% 0.19/0.55  fof(f204,plain,(
% 0.19/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.19/0.55    inference(forward_demodulation,[],[f203,f142])).
% 0.19/0.55  fof(f142,plain,(
% 0.19/0.55    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)),
% 0.19/0.55    inference(superposition,[],[f70,f66])).
% 0.19/0.55  fof(f66,plain,(
% 0.19/0.55    ( ! [X1] : (k3_xboole_0(X1,sK2) = k9_subset_1(k2_struct_0(sK0),X1,sK2)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f64,f62])).
% 0.19/0.55  fof(f64,plain,(
% 0.19/0.55    ( ! [X1] : (k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),X1,sK2)) )),
% 0.19/0.55    inference(resolution,[],[f50,f37])).
% 0.19/0.55  fof(f50,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f19])).
% 0.19/0.55  fof(f19,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f4])).
% 0.19/0.55  fof(f4,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.55  fof(f70,plain,(
% 0.19/0.55    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f69,f65])).
% 0.19/0.55  fof(f65,plain,(
% 0.19/0.55    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK0),X0,sK1)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f63,f62])).
% 0.19/0.55  fof(f63,plain,(
% 0.19/0.55    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)) )),
% 0.19/0.55    inference(resolution,[],[f50,f35])).
% 0.19/0.55  fof(f35,plain,(
% 0.19/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.55    inference(cnf_transformation,[],[f26])).
% 0.19/0.55  fof(f69,plain,(
% 0.19/0.55    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK1) = k9_subset_1(k2_struct_0(sK0),sK1,X0)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f67,f62])).
% 0.19/0.55  fof(f67,plain,(
% 0.19/0.55    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 0.19/0.55    inference(resolution,[],[f51,f35])).
% 0.19/0.55  fof(f51,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f20])).
% 0.19/0.55  fof(f20,plain,(
% 0.19/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f3])).
% 0.19/0.55  fof(f3,axiom,(
% 0.19/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.19/0.55  fof(f203,plain,(
% 0.19/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.19/0.55    inference(forward_demodulation,[],[f197,f65])).
% 0.19/0.55  fof(f197,plain,(
% 0.19/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 0.19/0.55    inference(superposition,[],[f39,f62])).
% 0.19/0.55  fof(f39,plain,(
% 0.19/0.55    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 0.19/0.55    inference(cnf_transformation,[],[f26])).
% 0.19/0.55  fof(f295,plain,(
% 0.19/0.55    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~spl4_11),
% 0.19/0.55    inference(forward_demodulation,[],[f294,f184])).
% 0.19/0.55  fof(f184,plain,(
% 0.19/0.55    sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) | ~spl4_11),
% 0.19/0.55    inference(avatar_component_clause,[],[f182])).
% 0.19/0.55  fof(f294,plain,(
% 0.19/0.55    k2_pre_topc(sK0,k3_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.19/0.55    inference(forward_demodulation,[],[f293,f142])).
% 0.19/0.55  fof(f293,plain,(
% 0.19/0.55    k2_pre_topc(sK0,k3_xboole_0(k2_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))),
% 0.19/0.55    inference(forward_demodulation,[],[f292,f72])).
% 0.19/0.55  fof(f72,plain,(
% 0.19/0.55    ( ! [X1] : (k3_xboole_0(X1,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X1)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f71,f66])).
% 0.19/0.55  fof(f71,plain,(
% 0.19/0.55    ( ! [X1] : (k9_subset_1(k2_struct_0(sK0),X1,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X1)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f68,f62])).
% 0.19/0.55  fof(f68,plain,(
% 0.19/0.55    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)) )),
% 0.19/0.55    inference(resolution,[],[f51,f37])).
% 0.19/0.55  fof(f292,plain,(
% 0.19/0.55    k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 0.19/0.55    inference(subsumption_resolution,[],[f286,f38])).
% 0.19/0.55  fof(f38,plain,(
% 0.19/0.55    v3_pre_topc(sK2,sK0)),
% 0.19/0.55    inference(cnf_transformation,[],[f26])).
% 0.19/0.55  fof(f286,plain,(
% 0.19/0.55    k2_pre_topc(sK0,k3_xboole_0(sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) | ~v3_pre_topc(sK2,sK0)),
% 0.19/0.55    inference(resolution,[],[f198,f98])).
% 0.19/0.55  fof(f98,plain,(
% 0.19/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k3_xboole_0(X0,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 0.19/0.55    inference(forward_demodulation,[],[f97,f62])).
% 0.19/0.55  fof(f97,plain,(
% 0.19/0.55    ( ! [X0] : (k2_pre_topc(sK0,k3_xboole_0(X0,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.55    inference(forward_demodulation,[],[f96,f76])).
% 0.19/0.55  fof(f76,plain,(
% 0.19/0.55    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.19/0.55    inference(subsumption_resolution,[],[f75,f34])).
% 0.19/0.55  fof(f75,plain,(
% 0.19/0.55    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.19/0.55    inference(subsumption_resolution,[],[f73,f36])).
% 0.19/0.55  fof(f36,plain,(
% 0.19/0.55    v1_tops_1(sK1,sK0)),
% 0.19/0.55    inference(cnf_transformation,[],[f26])).
% 0.19/0.55  fof(f73,plain,(
% 0.19/0.55    ~v1_tops_1(sK1,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.19/0.55    inference(resolution,[],[f42,f35])).
% 0.19/0.55  fof(f42,plain,(
% 0.19/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f27])).
% 0.19/0.55  fof(f27,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(nnf_transformation,[],[f16])).
% 0.19/0.55  fof(f16,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.55    inference(ennf_transformation,[],[f8])).
% 0.19/0.55  fof(f8,axiom,(
% 0.19/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.19/0.55  fof(f96,plain,(
% 0.19/0.55    ( ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k3_xboole_0(X0,sK1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.55    inference(forward_demodulation,[],[f95,f65])).
% 0.19/0.55  fof(f95,plain,(
% 0.19/0.55    ( ! [X0] : (k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,sK1)) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.55    inference(forward_demodulation,[],[f94,f62])).
% 0.19/0.55  fof(f94,plain,(
% 0.19/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.55    inference(subsumption_resolution,[],[f93,f33])).
% 0.19/0.55  fof(f33,plain,(
% 0.19/0.55    v2_pre_topc(sK0)),
% 0.19/0.55    inference(cnf_transformation,[],[f26])).
% 0.19/0.55  fof(f93,plain,(
% 0.19/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) )),
% 0.19/0.55    inference(subsumption_resolution,[],[f91,f34])).
% 0.19/0.55  fof(f91,plain,(
% 0.19/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.55    inference(resolution,[],[f44,f35])).
% 0.19/0.55  fof(f44,plain,(
% 0.19/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.55    inference(cnf_transformation,[],[f18])).
% 0.19/0.55  fof(f18,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.55    inference(flattening,[],[f17])).
% 0.19/0.55  fof(f17,plain,(
% 0.19/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.55    inference(ennf_transformation,[],[f9])).
% 0.19/0.55  fof(f9,axiom,(
% 0.19/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 0.19/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
% 0.19/0.55  fof(f198,plain,(
% 0.19/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.19/0.55    inference(superposition,[],[f37,f62])).
% 0.19/0.55  % SZS output end Proof for theBenchmark
% 0.19/0.55  % (7609)------------------------------
% 0.19/0.55  % (7609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.55  % (7609)Termination reason: Refutation
% 0.19/0.55  
% 0.19/0.55  % (7609)Memory used [KB]: 10746
% 0.19/0.55  % (7609)Time elapsed: 0.098 s
% 0.19/0.55  % (7609)------------------------------
% 0.19/0.55  % (7609)------------------------------
% 0.19/0.55  % (7614)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.55  % (7596)Success in time 0.199 s
%------------------------------------------------------------------------------
