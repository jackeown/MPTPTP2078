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
% DateTime   : Thu Dec  3 13:11:40 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 587 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   28
%              Number of atoms          :  377 (2911 expanded)
%              Number of equality atoms :  106 ( 814 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f161,f3493,f3942])).

fof(f3942,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3941])).

fof(f3941,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f3923,f159])).

fof(f159,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3923,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f140,f3921])).

fof(f3921,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f3920,f608])).

fof(f608,plain,(
    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f597,f113])).

fof(f113,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f597,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f594,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f594,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f101,f372])).

fof(f372,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f139,f127])).

fof(f127,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f78,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f78,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f68,f70,f69])).

fof(f69,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f139,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f125,f77])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f125,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3920,plain,
    ( k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f3917,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
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

fof(f3917,plain,
    ( ~ r1_tarski(sK1,sK1)
    | k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f3643,f78])).

fof(f3643,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X8)
        | k1_tops_1(sK0,X8) = k2_xboole_0(sK1,k1_tops_1(sK0,X8)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f3499,f100])).

fof(f3499,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f3498,f77])).

fof(f3498,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f3497,f78])).

fof(f3497,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_1 ),
    inference(resolution,[],[f156,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f156,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f140,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f126,f77])).

fof(f126,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f3493,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f3492])).

fof(f3492,plain,
    ( $false
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3491,f76])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f3491,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3490,f77])).

fof(f3490,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3489,f78])).

fof(f3489,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f3482,f186])).

fof(f186,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f80,f160])).

fof(f160,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f158])).

fof(f80,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

fof(f3482,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f91,f3385])).

fof(f3385,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f372,f3374])).

fof(f3374,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f3353,f3111])).

fof(f3111,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3046,f105])).

fof(f105,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3046,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))) ),
    inference(superposition,[],[f152,f376])).

fof(f376,plain,(
    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f361,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f361,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f340,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f340,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f339,f78])).

fof(f339,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f338,f276])).

fof(f276,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f275,f77])).

fof(f275,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f274,f214])).

fof(f214,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f213,f78])).

fof(f213,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f110,f131])).

fof(f131,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f78,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f274,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f89,f247])).

fof(f247,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f137,f131])).

fof(f137,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f123,f77])).

fof(f123,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f338,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f112,f138])).

fof(f138,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f124,f77])).

fof(f124,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f78,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f152,plain,(
    ! [X0] : k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f151,f113])).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X0),sK1) ),
    inference(forward_demodulation,[],[f146,f105])).

fof(f146,plain,(
    ! [X0] : k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f118,f143])).

fof(f143,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f130,f98])).

fof(f130,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f78,f93])).

fof(f118,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f102,f104])).

fof(f104,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f102,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f3353,plain,
    ( k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f336,f3344])).

fof(f3344,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(superposition,[],[f358,f160])).

fof(f358,plain,(
    ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f340,f84])).

fof(f336,plain,(
    ! [X0] : k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f331,f113])).

fof(f331,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f118,f310])).

fof(f310,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f136,f132])).

fof(f132,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,X3) = X3 ),
    inference(resolution,[],[f78,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f136,plain,(
    ! [X6] : k9_subset_1(u1_struct_0(sK0),X6,sK1) = k4_xboole_0(X6,k4_xboole_0(X6,sK1)) ),
    inference(resolution,[],[f78,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f106,f104])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f161,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f79,f158,f154])).

fof(f79,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:00:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (9444)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (9432)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9437)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (9452)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (9426)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (9428)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (9429)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (9455)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (9454)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (9435)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (9430)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (9431)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (9427)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (9449)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (9441)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (9448)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (9451)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (9447)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (9446)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (9434)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (9436)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (9450)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (9440)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.56  % (9442)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (9439)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (9443)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (9433)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.59  % (9453)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.59  % (9445)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.59  % (9438)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 3.20/0.82  % (9450)Refutation found. Thanks to Tanya!
% 3.20/0.82  % SZS status Theorem for theBenchmark
% 3.20/0.82  % SZS output start Proof for theBenchmark
% 3.20/0.82  fof(f3943,plain,(
% 3.20/0.82    $false),
% 3.20/0.82    inference(avatar_sat_refutation,[],[f161,f3493,f3942])).
% 3.20/0.82  fof(f3942,plain,(
% 3.20/0.82    ~spl2_1 | spl2_2),
% 3.20/0.82    inference(avatar_contradiction_clause,[],[f3941])).
% 3.20/0.82  fof(f3941,plain,(
% 3.20/0.82    $false | (~spl2_1 | spl2_2)),
% 3.20/0.82    inference(subsumption_resolution,[],[f3923,f159])).
% 3.20/0.82  fof(f159,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 3.20/0.82    inference(avatar_component_clause,[],[f158])).
% 3.20/0.82  fof(f158,plain,(
% 3.20/0.82    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.20/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.20/0.82  fof(f3923,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_1),
% 3.20/0.82    inference(backward_demodulation,[],[f140,f3921])).
% 3.20/0.82  fof(f3921,plain,(
% 3.20/0.82    sK1 = k1_tops_1(sK0,sK1) | ~spl2_1),
% 3.20/0.82    inference(forward_demodulation,[],[f3920,f608])).
% 3.20/0.82  fof(f608,plain,(
% 3.20/0.82    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 3.20/0.82    inference(superposition,[],[f597,f113])).
% 3.20/0.82  fof(f113,plain,(
% 3.20/0.82    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f1])).
% 3.20/0.82  fof(f1,axiom,(
% 3.20/0.82    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.20/0.82  fof(f597,plain,(
% 3.20/0.82    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 3.20/0.82    inference(resolution,[],[f594,f100])).
% 3.20/0.82  fof(f100,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 3.20/0.82    inference(cnf_transformation,[],[f56])).
% 3.20/0.82  fof(f56,plain,(
% 3.20/0.82    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.20/0.82    inference(ennf_transformation,[],[f6])).
% 3.20/0.82  fof(f6,axiom,(
% 3.20/0.82    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.20/0.82  fof(f594,plain,(
% 3.20/0.82    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.20/0.82    inference(superposition,[],[f101,f372])).
% 3.20/0.82  fof(f372,plain,(
% 3.20/0.82    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.20/0.82    inference(superposition,[],[f139,f127])).
% 3.20/0.82  fof(f127,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 3.20/0.82    inference(resolution,[],[f78,f84])).
% 3.20/0.82  fof(f84,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f40])).
% 3.20/0.82  fof(f40,plain,(
% 3.20/0.82    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f22])).
% 3.20/0.82  fof(f22,axiom,(
% 3.20/0.82    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.20/0.82  fof(f78,plain,(
% 3.20/0.82    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(cnf_transformation,[],[f71])).
% 3.20/0.82  fof(f71,plain,(
% 3.20/0.82    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.20/0.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f68,f70,f69])).
% 3.20/0.82  fof(f69,plain,(
% 3.20/0.82    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.20/0.82    introduced(choice_axiom,[])).
% 3.20/0.82  fof(f70,plain,(
% 3.20/0.82    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.20/0.82    introduced(choice_axiom,[])).
% 3.20/0.82  fof(f68,plain,(
% 3.20/0.82    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.82    inference(flattening,[],[f67])).
% 3.20/0.82  fof(f67,plain,(
% 3.20/0.82    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.82    inference(nnf_transformation,[],[f39])).
% 3.20/0.82  fof(f39,plain,(
% 3.20/0.82    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.20/0.82    inference(flattening,[],[f38])).
% 3.20/0.82  fof(f38,plain,(
% 3.20/0.82    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f37])).
% 3.20/0.82  fof(f37,negated_conjecture,(
% 3.20/0.82    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.20/0.82    inference(negated_conjecture,[],[f36])).
% 3.20/0.82  fof(f36,conjecture,(
% 3.20/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.20/0.82  fof(f139,plain,(
% 3.20/0.82    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.20/0.82    inference(subsumption_resolution,[],[f125,f77])).
% 3.20/0.82  fof(f77,plain,(
% 3.20/0.82    l1_pre_topc(sK0)),
% 3.20/0.82    inference(cnf_transformation,[],[f71])).
% 3.20/0.82  fof(f125,plain,(
% 3.20/0.82    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(resolution,[],[f78,f87])).
% 3.20/0.82  fof(f87,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f43])).
% 3.20/0.82  fof(f43,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(ennf_transformation,[],[f35])).
% 3.20/0.82  fof(f35,axiom,(
% 3.20/0.82    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.20/0.82  fof(f101,plain,(
% 3.20/0.82    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f10])).
% 3.20/0.82  fof(f10,axiom,(
% 3.20/0.82    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.20/0.82  fof(f3920,plain,(
% 3.20/0.82    k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_1),
% 3.20/0.82    inference(subsumption_resolution,[],[f3917,f122])).
% 3.20/0.82  fof(f122,plain,(
% 3.20/0.82    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.20/0.82    inference(equality_resolution,[],[f81])).
% 3.20/0.82  fof(f81,plain,(
% 3.20/0.82    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.20/0.82    inference(cnf_transformation,[],[f73])).
% 3.20/0.82  fof(f73,plain,(
% 3.20/0.82    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.82    inference(flattening,[],[f72])).
% 3.20/0.82  fof(f72,plain,(
% 3.20/0.82    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.20/0.82    inference(nnf_transformation,[],[f3])).
% 3.20/0.82  fof(f3,axiom,(
% 3.20/0.82    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.20/0.82  fof(f3917,plain,(
% 3.20/0.82    ~r1_tarski(sK1,sK1) | k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl2_1),
% 3.20/0.82    inference(resolution,[],[f3643,f78])).
% 3.20/0.82  fof(f3643,plain,(
% 3.20/0.82    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X8) | k1_tops_1(sK0,X8) = k2_xboole_0(sK1,k1_tops_1(sK0,X8))) ) | ~spl2_1),
% 3.20/0.82    inference(resolution,[],[f3499,f100])).
% 3.20/0.82  fof(f3499,plain,(
% 3.20/0.82    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_1),
% 3.20/0.82    inference(subsumption_resolution,[],[f3498,f77])).
% 3.20/0.82  fof(f3498,plain,(
% 3.20/0.82    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 3.20/0.82    inference(subsumption_resolution,[],[f3497,f78])).
% 3.20/0.82  fof(f3497,plain,(
% 3.20/0.82    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_1),
% 3.20/0.82    inference(resolution,[],[f156,f92])).
% 3.20/0.82  fof(f92,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f51])).
% 3.20/0.82  fof(f51,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(flattening,[],[f50])).
% 3.20/0.82  fof(f50,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(ennf_transformation,[],[f32])).
% 3.20/0.82  fof(f32,axiom,(
% 3.20/0.82    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.20/0.82  fof(f156,plain,(
% 3.20/0.82    v3_pre_topc(sK1,sK0) | ~spl2_1),
% 3.20/0.82    inference(avatar_component_clause,[],[f154])).
% 3.20/0.82  fof(f154,plain,(
% 3.20/0.82    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 3.20/0.82    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.20/0.82  fof(f140,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.20/0.82    inference(subsumption_resolution,[],[f126,f77])).
% 3.20/0.82  fof(f126,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(resolution,[],[f78,f86])).
% 3.20/0.82  fof(f86,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f42])).
% 3.20/0.82  fof(f42,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(ennf_transformation,[],[f31])).
% 3.20/0.82  fof(f31,axiom,(
% 3.20/0.82    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.20/0.82  fof(f3493,plain,(
% 3.20/0.82    ~spl2_2),
% 3.20/0.82    inference(avatar_contradiction_clause,[],[f3492])).
% 3.20/0.82  fof(f3492,plain,(
% 3.20/0.82    $false | ~spl2_2),
% 3.20/0.82    inference(subsumption_resolution,[],[f3491,f76])).
% 3.20/0.82  fof(f76,plain,(
% 3.20/0.82    v2_pre_topc(sK0)),
% 3.20/0.82    inference(cnf_transformation,[],[f71])).
% 3.20/0.82  fof(f3491,plain,(
% 3.20/0.82    ~v2_pre_topc(sK0) | ~spl2_2),
% 3.20/0.82    inference(subsumption_resolution,[],[f3490,f77])).
% 3.20/0.82  fof(f3490,plain,(
% 3.20/0.82    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_2),
% 3.20/0.82    inference(subsumption_resolution,[],[f3489,f78])).
% 3.20/0.82  fof(f3489,plain,(
% 3.20/0.82    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_2),
% 3.20/0.82    inference(subsumption_resolution,[],[f3482,f186])).
% 3.20/0.82  fof(f186,plain,(
% 3.20/0.82    ~v3_pre_topc(sK1,sK0) | ~spl2_2),
% 3.20/0.82    inference(subsumption_resolution,[],[f80,f160])).
% 3.20/0.82  fof(f160,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.20/0.82    inference(avatar_component_clause,[],[f158])).
% 3.20/0.82  fof(f80,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.20/0.82    inference(cnf_transformation,[],[f71])).
% 3.20/0.82  fof(f3482,plain,(
% 3.20/0.82    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_2),
% 3.20/0.82    inference(superposition,[],[f91,f3385])).
% 3.20/0.82  fof(f3385,plain,(
% 3.20/0.82    sK1 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 3.20/0.82    inference(backward_demodulation,[],[f372,f3374])).
% 3.20/0.82  fof(f3374,plain,(
% 3.20/0.82    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 3.20/0.82    inference(forward_demodulation,[],[f3353,f3111])).
% 3.20/0.82  fof(f3111,plain,(
% 3.20/0.82    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)))),
% 3.20/0.82    inference(forward_demodulation,[],[f3046,f105])).
% 3.20/0.82  fof(f105,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.82    inference(cnf_transformation,[],[f11])).
% 3.20/0.82  fof(f11,axiom,(
% 3.20/0.82    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.20/0.82  fof(f3046,plain,(
% 3.20/0.82    k4_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1)))),
% 3.20/0.82    inference(superposition,[],[f152,f376])).
% 3.20/0.82  fof(f376,plain,(
% 3.20/0.82    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 3.20/0.82    inference(resolution,[],[f361,f98])).
% 3.20/0.82  fof(f98,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.20/0.82    inference(cnf_transformation,[],[f75])).
% 3.20/0.82  fof(f75,plain,(
% 3.20/0.82    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.20/0.82    inference(nnf_transformation,[],[f4])).
% 3.20/0.82  fof(f4,axiom,(
% 3.20/0.82    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.20/0.82  fof(f361,plain,(
% 3.20/0.82    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 3.20/0.82    inference(resolution,[],[f340,f93])).
% 3.20/0.82  fof(f93,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f74])).
% 3.20/0.82  fof(f74,plain,(
% 3.20/0.82    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.20/0.82    inference(nnf_transformation,[],[f27])).
% 3.20/0.82  fof(f27,axiom,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.20/0.82  fof(f340,plain,(
% 3.20/0.82    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(subsumption_resolution,[],[f339,f78])).
% 3.20/0.82  fof(f339,plain,(
% 3.20/0.82    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(subsumption_resolution,[],[f338,f276])).
% 3.20/0.82  fof(f276,plain,(
% 3.20/0.82    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(subsumption_resolution,[],[f275,f77])).
% 3.20/0.82  fof(f275,plain,(
% 3.20/0.82    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(subsumption_resolution,[],[f274,f214])).
% 3.20/0.82  fof(f214,plain,(
% 3.20/0.82    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(subsumption_resolution,[],[f213,f78])).
% 3.20/0.82  fof(f213,plain,(
% 3.20/0.82    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(superposition,[],[f110,f131])).
% 3.20/0.82  fof(f131,plain,(
% 3.20/0.82    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 3.20/0.82    inference(resolution,[],[f78,f103])).
% 3.20/0.82  fof(f103,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f57])).
% 3.20/0.82  fof(f57,plain,(
% 3.20/0.82    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f15])).
% 3.20/0.82  fof(f15,axiom,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.20/0.82  fof(f110,plain,(
% 3.20/0.82    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/0.82    inference(cnf_transformation,[],[f62])).
% 3.20/0.82  fof(f62,plain,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f16])).
% 3.20/0.82  fof(f16,axiom,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.20/0.82  fof(f274,plain,(
% 3.20/0.82    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(superposition,[],[f89,f247])).
% 3.20/0.82  fof(f247,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 3.20/0.82    inference(forward_demodulation,[],[f137,f131])).
% 3.20/0.82  fof(f137,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 3.20/0.82    inference(subsumption_resolution,[],[f123,f77])).
% 3.20/0.82  fof(f123,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(resolution,[],[f78,f90])).
% 3.20/0.82  fof(f90,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f47])).
% 3.20/0.82  fof(f47,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(ennf_transformation,[],[f33])).
% 3.20/0.82  fof(f33,axiom,(
% 3.20/0.82    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 3.20/0.82  fof(f89,plain,(
% 3.20/0.82    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f46])).
% 3.20/0.82  fof(f46,plain,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(flattening,[],[f45])).
% 3.20/0.82  fof(f45,plain,(
% 3.20/0.82    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f29])).
% 3.20/0.82  fof(f29,axiom,(
% 3.20/0.82    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.20/0.82  fof(f338,plain,(
% 3.20/0.82    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.20/0.82    inference(superposition,[],[f112,f138])).
% 3.20/0.82  fof(f138,plain,(
% 3.20/0.82    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.20/0.82    inference(subsumption_resolution,[],[f124,f77])).
% 3.20/0.82  fof(f124,plain,(
% 3.20/0.82    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.20/0.82    inference(resolution,[],[f78,f88])).
% 3.20/0.82  fof(f88,plain,(
% 3.20/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f44])).
% 3.20/0.82  fof(f44,plain,(
% 3.20/0.82    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.20/0.82    inference(ennf_transformation,[],[f34])).
% 3.20/0.82  fof(f34,axiom,(
% 3.20/0.82    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.20/0.82  fof(f112,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.20/0.82    inference(cnf_transformation,[],[f66])).
% 3.20/0.82  fof(f66,plain,(
% 3.20/0.82    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(flattening,[],[f65])).
% 3.20/0.82  fof(f65,plain,(
% 3.20/0.82    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.20/0.82    inference(ennf_transformation,[],[f17])).
% 3.20/0.82  fof(f17,axiom,(
% 3.20/0.82    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.20/0.82  fof(f152,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(sK1,k4_xboole_0(sK1,X0))) )),
% 3.20/0.82    inference(forward_demodulation,[],[f151,f113])).
% 3.20/0.82  fof(f151,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X0),sK1)) )),
% 3.20/0.82    inference(forward_demodulation,[],[f146,f105])).
% 3.20/0.82  fof(f146,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(X0,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X0),k4_xboole_0(sK1,k1_xboole_0))) )),
% 3.20/0.82    inference(superposition,[],[f118,f143])).
% 3.20/0.82  fof(f143,plain,(
% 3.20/0.82    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))),
% 3.20/0.82    inference(resolution,[],[f130,f98])).
% 3.20/0.82  fof(f130,plain,(
% 3.20/0.82    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.20/0.82    inference(resolution,[],[f78,f93])).
% 3.20/0.82  fof(f118,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 3.20/0.82    inference(definition_unfolding,[],[f102,f104])).
% 3.20/0.82  fof(f104,plain,(
% 3.20/0.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.20/0.82    inference(cnf_transformation,[],[f13])).
% 3.20/0.82  fof(f13,axiom,(
% 3.20/0.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.20/0.82  fof(f102,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.20/0.82    inference(cnf_transformation,[],[f14])).
% 3.20/0.82  fof(f14,axiom,(
% 3.20/0.82    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 3.20/0.82  fof(f3353,plain,(
% 3.20/0.82    k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k4_xboole_0(sK1,k2_pre_topc(sK0,sK1))) | ~spl2_2),
% 3.20/0.82    inference(superposition,[],[f336,f3344])).
% 3.20/0.82  fof(f3344,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.20/0.82    inference(superposition,[],[f358,f160])).
% 3.20/0.82  fof(f358,plain,(
% 3.20/0.82    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) )),
% 3.20/0.82    inference(resolution,[],[f340,f84])).
% 3.20/0.82  fof(f336,plain,(
% 3.20/0.82    ( ! [X0] : (k2_xboole_0(sK1,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) )),
% 3.20/0.82    inference(forward_demodulation,[],[f331,f113])).
% 3.20/0.82  fof(f331,plain,(
% 3.20/0.82    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) )),
% 3.20/0.82    inference(superposition,[],[f118,f310])).
% 3.20/0.82  fof(f310,plain,(
% 3.20/0.82    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 3.20/0.82    inference(superposition,[],[f136,f132])).
% 3.20/0.82  fof(f132,plain,(
% 3.20/0.82    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),X3,X3) = X3) )),
% 3.20/0.82    inference(resolution,[],[f78,f108])).
% 3.20/0.82  fof(f108,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 3.20/0.82    inference(cnf_transformation,[],[f60])).
% 3.20/0.82  fof(f60,plain,(
% 3.20/0.82    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f19])).
% 3.20/0.82  fof(f19,axiom,(
% 3.20/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.20/0.82  fof(f136,plain,(
% 3.20/0.82    ( ! [X6] : (k9_subset_1(u1_struct_0(sK0),X6,sK1) = k4_xboole_0(X6,k4_xboole_0(X6,sK1))) )),
% 3.20/0.82    inference(resolution,[],[f78,f119])).
% 3.20/0.82  fof(f119,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 3.20/0.82    inference(definition_unfolding,[],[f106,f104])).
% 3.20/0.82  fof(f106,plain,(
% 3.20/0.82    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.20/0.82    inference(cnf_transformation,[],[f58])).
% 3.20/0.82  fof(f58,plain,(
% 3.20/0.82    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f23])).
% 3.20/0.82  fof(f23,axiom,(
% 3.20/0.82    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 3.20/0.82  fof(f91,plain,(
% 3.20/0.82    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.20/0.82    inference(cnf_transformation,[],[f49])).
% 3.20/0.82  fof(f49,plain,(
% 3.20/0.82    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.20/0.82    inference(flattening,[],[f48])).
% 3.20/0.82  fof(f48,plain,(
% 3.20/0.82    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.20/0.82    inference(ennf_transformation,[],[f30])).
% 3.20/0.82  fof(f30,axiom,(
% 3.20/0.82    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.20/0.82    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.20/0.82  fof(f161,plain,(
% 3.20/0.82    spl2_1 | spl2_2),
% 3.20/0.82    inference(avatar_split_clause,[],[f79,f158,f154])).
% 3.20/0.82  fof(f79,plain,(
% 3.20/0.82    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.20/0.82    inference(cnf_transformation,[],[f71])).
% 3.20/0.82  % SZS output end Proof for theBenchmark
% 3.20/0.82  % (9450)------------------------------
% 3.20/0.82  % (9450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (9450)Termination reason: Refutation
% 3.20/0.82  
% 3.20/0.82  % (9450)Memory used [KB]: 12920
% 3.20/0.82  % (9450)Time elapsed: 0.366 s
% 3.20/0.82  % (9450)------------------------------
% 3.20/0.82  % (9450)------------------------------
% 3.20/0.82  % (9428)Time limit reached!
% 3.20/0.82  % (9428)------------------------------
% 3.20/0.82  % (9428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (9428)Termination reason: Time limit
% 3.20/0.82  
% 3.20/0.82  % (9428)Memory used [KB]: 6268
% 3.20/0.82  % (9428)Time elapsed: 0.404 s
% 3.20/0.82  % (9428)------------------------------
% 3.20/0.82  % (9428)------------------------------
% 3.20/0.83  % (9425)Success in time 0.464 s
%------------------------------------------------------------------------------
