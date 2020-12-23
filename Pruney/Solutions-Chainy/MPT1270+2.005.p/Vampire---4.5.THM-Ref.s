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
% DateTime   : Thu Dec  3 13:12:36 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 243 expanded)
%              Number of leaves         :   18 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  248 (1041 expanded)
%              Number of equality atoms :   43 (  57 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f903,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f67,f870,f878,f900])).

fof(f900,plain,
    ( spl2_2
    | ~ spl2_21 ),
    inference(avatar_contradiction_clause,[],[f899])).

fof(f899,plain,
    ( $false
    | spl2_2
    | ~ spl2_21 ),
    inference(subsumption_resolution,[],[f892,f92])).

fof(f92,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).

fof(f30,plain,
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

fof(f31,plain,
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).

fof(f91,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f892,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_2
    | ~ spl2_21 ),
    inference(superposition,[],[f65,f890])).

fof(f890,plain,
    ( k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1)
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f888,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f888,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ spl2_21 ),
    inference(superposition,[],[f882,f121])).

fof(f121,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f95,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f95,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f882,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0)
    | ~ spl2_21 ),
    inference(superposition,[],[f103,f874])).

fof(f874,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f873])).

fof(f873,plain,
    ( spl2_21
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f103,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f43,f37])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f65,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f878,plain,
    ( spl2_21
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f877,f59,f873])).

fof(f59,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f877,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f96,f36])).

fof(f96,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f44,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f870,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f854])).

fof(f854,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(resolution,[],[f338,f230])).

fof(f230,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1))
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f229,f99])).

fof(f99,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f98,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f97,f61])).

fof(f61,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f97,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f229,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f202,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f202,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f197,f140])).

fof(f140,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f101,f93])).

fof(f93,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(resolution,[],[f52,f37])).

fof(f101,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f100,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f37])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f197,plain,
    ( r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_xboole_0)
    | ~ spl2_2 ),
    inference(resolution,[],[f165,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_xboole_0(X1,X0))
      | r1_tarski(k4_xboole_0(X2,X0),X1) ) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f165,plain,
    ( r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1)))
    | ~ spl2_2 ),
    inference(resolution,[],[f90,f64])).

fof(f64,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1)) ) ),
    inference(superposition,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f338,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f184,f40])).

fof(f184,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f86,f88])).

fof(f88,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f54,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f67,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f38,f63,f59])).

fof(f38,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f66,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f39,f63,f59])).

fof(f39,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:30:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (31372)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.47  % (31380)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (31365)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.23/0.51  % (31371)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.23/0.51  % (31368)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.23/0.51  % (31361)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.51  % (31369)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.23/0.52  % (31374)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.23/0.52  % (31367)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.23/0.52  % (31378)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.23/0.52  % (31360)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.23/0.52  % (31370)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.23/0.52  % (31376)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.23/0.52  % (31366)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.23/0.52  % (31364)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.23/0.53  % (31379)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.23/0.53  % (31381)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.34/0.53  % (31363)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.34/0.53  % (31382)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.34/0.53  % (31377)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.34/0.53  % (31385)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.34/0.53  % (31362)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.34/0.53  % (31373)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (31384)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.34/0.55  % (31375)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.34/0.55  % (31383)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.34/0.57  % (31370)Refutation found. Thanks to Tanya!
% 1.34/0.57  % SZS status Theorem for theBenchmark
% 1.34/0.57  % SZS output start Proof for theBenchmark
% 1.34/0.57  fof(f903,plain,(
% 1.34/0.57    $false),
% 1.34/0.57    inference(avatar_sat_refutation,[],[f66,f67,f870,f878,f900])).
% 1.34/0.57  fof(f900,plain,(
% 1.34/0.57    spl2_2 | ~spl2_21),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f899])).
% 1.34/0.57  fof(f899,plain,(
% 1.34/0.57    $false | (spl2_2 | ~spl2_21)),
% 1.34/0.57    inference(subsumption_resolution,[],[f892,f92])).
% 1.34/0.57  fof(f92,plain,(
% 1.34/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f91,f36])).
% 1.34/0.57  fof(f36,plain,(
% 1.34/0.57    l1_pre_topc(sK0)),
% 1.34/0.57    inference(cnf_transformation,[],[f32])).
% 1.34/0.57  fof(f32,plain,(
% 1.34/0.57    ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.34/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f31,f30])).
% 1.34/0.57  fof(f30,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f31,plain,(
% 1.34/0.57    ? [X1] : ((~r1_tarski(X1,k2_tops_1(sK0,X1)) | ~v2_tops_1(X1,sK0)) & (r1_tarski(X1,k2_tops_1(sK0,X1)) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)) & (r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.34/0.57    introduced(choice_axiom,[])).
% 1.34/0.57  fof(f29,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.34/0.57    inference(flattening,[],[f28])).
% 1.34/0.57  fof(f28,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.34/0.57    inference(nnf_transformation,[],[f16])).
% 1.34/0.57  fof(f16,plain,(
% 1.34/0.57    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f15])).
% 1.34/0.57  fof(f15,negated_conjecture,(
% 1.34/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.34/0.57    inference(negated_conjecture,[],[f14])).
% 1.34/0.57  fof(f14,conjecture,(
% 1.34/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tops_1)).
% 1.34/0.57  fof(f91,plain,(
% 1.34/0.57    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.34/0.57    inference(resolution,[],[f41,f37])).
% 1.34/0.57  fof(f37,plain,(
% 1.34/0.57    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.57    inference(cnf_transformation,[],[f32])).
% 1.34/0.57  fof(f41,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f17])).
% 1.34/0.57  fof(f17,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f10])).
% 1.34/0.57  fof(f10,axiom,(
% 1.34/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.34/0.57  fof(f892,plain,(
% 1.34/0.57    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (spl2_2 | ~spl2_21)),
% 1.34/0.57    inference(superposition,[],[f65,f890])).
% 1.34/0.57  fof(f890,plain,(
% 1.34/0.57    k2_tops_1(sK0,sK1) = k2_pre_topc(sK0,sK1) | ~spl2_21),
% 1.34/0.57    inference(forward_demodulation,[],[f888,f40])).
% 1.34/0.57  fof(f40,plain,(
% 1.34/0.57    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.34/0.57    inference(cnf_transformation,[],[f5])).
% 1.34/0.57  fof(f5,axiom,(
% 1.34/0.57    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.34/0.57  fof(f888,plain,(
% 1.34/0.57    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_xboole_0) | ~spl2_21),
% 1.34/0.57    inference(superposition,[],[f882,f121])).
% 1.34/0.57  fof(f121,plain,(
% 1.34/0.57    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)) )),
% 1.34/0.57    inference(resolution,[],[f95,f52])).
% 1.34/0.57  fof(f52,plain,(
% 1.34/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f23])).
% 1.34/0.57  fof(f23,plain,(
% 1.34/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f8])).
% 1.34/0.57  fof(f8,axiom,(
% 1.34/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.34/0.57  fof(f95,plain,(
% 1.34/0.57    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.34/0.57    inference(subsumption_resolution,[],[f94,f36])).
% 1.34/0.57  fof(f94,plain,(
% 1.34/0.57    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.34/0.57    inference(resolution,[],[f48,f37])).
% 1.34/0.57  fof(f48,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f22])).
% 1.34/0.57  fof(f22,plain,(
% 1.34/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.34/0.57    inference(flattening,[],[f21])).
% 1.34/0.57  fof(f21,plain,(
% 1.34/0.57    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.34/0.57    inference(ennf_transformation,[],[f9])).
% 1.34/0.57  fof(f9,axiom,(
% 1.34/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.34/0.57  fof(f882,plain,(
% 1.34/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_xboole_0) | ~spl2_21),
% 1.34/0.57    inference(superposition,[],[f103,f874])).
% 1.34/0.57  fof(f874,plain,(
% 1.34/0.57    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_21),
% 1.34/0.57    inference(avatar_component_clause,[],[f873])).
% 1.34/0.57  fof(f873,plain,(
% 1.34/0.57    spl2_21 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.34/0.57  fof(f103,plain,(
% 1.34/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 1.34/0.57    inference(subsumption_resolution,[],[f102,f36])).
% 1.34/0.57  fof(f102,plain,(
% 1.34/0.57    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.34/0.57    inference(resolution,[],[f43,f37])).
% 1.34/0.57  fof(f43,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f19])).
% 1.34/0.57  fof(f19,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f11])).
% 1.34/0.57  fof(f11,axiom,(
% 1.34/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 1.34/0.57  fof(f65,plain,(
% 1.34/0.57    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | spl2_2),
% 1.34/0.57    inference(avatar_component_clause,[],[f63])).
% 1.34/0.57  fof(f63,plain,(
% 1.34/0.57    spl2_2 <=> r1_tarski(sK1,k2_tops_1(sK0,sK1))),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.34/0.57  fof(f878,plain,(
% 1.34/0.57    spl2_21 | ~spl2_1),
% 1.34/0.57    inference(avatar_split_clause,[],[f877,f59,f873])).
% 1.34/0.57  fof(f59,plain,(
% 1.34/0.57    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 1.34/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.34/0.57  fof(f877,plain,(
% 1.34/0.57    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.34/0.57    inference(subsumption_resolution,[],[f96,f36])).
% 1.34/0.57  fof(f96,plain,(
% 1.34/0.57    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.34/0.57    inference(resolution,[],[f44,f37])).
% 1.34/0.57  fof(f44,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f33])).
% 1.34/0.57  fof(f33,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.57    inference(nnf_transformation,[],[f20])).
% 1.34/0.57  fof(f20,plain,(
% 1.34/0.57    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.57    inference(ennf_transformation,[],[f13])).
% 1.34/0.57  fof(f13,axiom,(
% 1.34/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.34/0.57  fof(f870,plain,(
% 1.34/0.57    spl2_1 | ~spl2_2),
% 1.34/0.57    inference(avatar_contradiction_clause,[],[f854])).
% 1.34/0.57  fof(f854,plain,(
% 1.34/0.57    $false | (spl2_1 | ~spl2_2)),
% 1.34/0.57    inference(resolution,[],[f338,f230])).
% 1.34/0.57  fof(f230,plain,(
% 1.34/0.57    ~r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1)) | (spl2_1 | ~spl2_2)),
% 1.34/0.57    inference(subsumption_resolution,[],[f229,f99])).
% 1.34/0.57  fof(f99,plain,(
% 1.34/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f98,f36])).
% 1.34/0.57  fof(f98,plain,(
% 1.34/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | spl2_1),
% 1.34/0.57    inference(subsumption_resolution,[],[f97,f61])).
% 1.34/0.57  fof(f61,plain,(
% 1.34/0.57    ~v2_tops_1(sK1,sK0) | spl2_1),
% 1.34/0.57    inference(avatar_component_clause,[],[f59])).
% 1.34/0.57  fof(f97,plain,(
% 1.34/0.57    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.34/0.57    inference(resolution,[],[f45,f37])).
% 1.34/0.57  fof(f45,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f33])).
% 1.34/0.57  fof(f229,plain,(
% 1.34/0.57    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_xboole_0,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 1.34/0.57    inference(resolution,[],[f202,f51])).
% 1.34/0.57  fof(f51,plain,(
% 1.34/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.34/0.57    inference(cnf_transformation,[],[f35])).
% 1.34/0.57  fof(f35,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(flattening,[],[f34])).
% 1.34/0.57  fof(f34,plain,(
% 1.34/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.34/0.57    inference(nnf_transformation,[],[f2])).
% 1.34/0.57  fof(f2,axiom,(
% 1.34/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.34/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.34/0.57  fof(f202,plain,(
% 1.34/0.57    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl2_2),
% 1.34/0.57    inference(forward_demodulation,[],[f197,f140])).
% 1.34/0.58  fof(f140,plain,(
% 1.34/0.58    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 1.34/0.58    inference(superposition,[],[f101,f93])).
% 1.34/0.58  fof(f93,plain,(
% 1.34/0.58    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)) )),
% 1.34/0.58    inference(resolution,[],[f52,f37])).
% 1.34/0.58  fof(f101,plain,(
% 1.34/0.58    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 1.34/0.58    inference(subsumption_resolution,[],[f100,f36])).
% 1.34/0.58  fof(f100,plain,(
% 1.34/0.58    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.34/0.58    inference(resolution,[],[f42,f37])).
% 1.34/0.58  fof(f42,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f18])).
% 1.34/0.58  fof(f18,plain,(
% 1.34/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.34/0.58    inference(ennf_transformation,[],[f12])).
% 1.34/0.58  fof(f12,axiom,(
% 1.34/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 1.34/0.58  fof(f197,plain,(
% 1.34/0.58    r1_tarski(k4_xboole_0(sK1,k2_tops_1(sK0,sK1)),k1_xboole_0) | ~spl2_2),
% 1.34/0.58    inference(resolution,[],[f165,f86])).
% 1.34/0.58  fof(f86,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_xboole_0(X1,X0)) | r1_tarski(k4_xboole_0(X2,X0),X1)) )),
% 1.34/0.58    inference(superposition,[],[f53,f47])).
% 1.34/0.58  fof(f47,plain,(
% 1.34/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f1])).
% 1.34/0.58  fof(f1,axiom,(
% 1.34/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.34/0.58  fof(f53,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f24])).
% 1.34/0.58  fof(f24,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.34/0.58    inference(ennf_transformation,[],[f6])).
% 1.34/0.58  fof(f6,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 1.34/0.58  fof(f165,plain,(
% 1.34/0.58    r1_tarski(sK1,k2_xboole_0(k1_xboole_0,k2_tops_1(sK0,sK1))) | ~spl2_2),
% 1.34/0.58    inference(resolution,[],[f90,f64])).
% 1.34/0.58  fof(f64,plain,(
% 1.34/0.58    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~spl2_2),
% 1.34/0.58    inference(avatar_component_clause,[],[f63])).
% 1.34/0.58  fof(f90,plain,(
% 1.34/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 1.34/0.58    inference(superposition,[],[f54,f40])).
% 1.34/0.58  fof(f54,plain,(
% 1.34/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.34/0.58    inference(cnf_transformation,[],[f25])).
% 1.34/0.58  fof(f25,plain,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.34/0.58    inference(ennf_transformation,[],[f7])).
% 1.34/0.58  fof(f7,axiom,(
% 1.34/0.58    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 1.34/0.58  fof(f338,plain,(
% 1.34/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.34/0.58    inference(superposition,[],[f184,f40])).
% 1.34/0.58  fof(f184,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.34/0.58    inference(resolution,[],[f86,f88])).
% 1.34/0.58  fof(f88,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.34/0.58    inference(resolution,[],[f54,f46])).
% 1.34/0.58  fof(f46,plain,(
% 1.34/0.58    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.34/0.58    inference(cnf_transformation,[],[f4])).
% 1.34/0.58  fof(f4,axiom,(
% 1.34/0.58    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.34/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.34/0.58  fof(f67,plain,(
% 1.34/0.58    spl2_1 | spl2_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f38,f63,f59])).
% 1.34/0.58  fof(f38,plain,(
% 1.34/0.58    r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.34/0.58    inference(cnf_transformation,[],[f32])).
% 1.34/0.58  fof(f66,plain,(
% 1.34/0.58    ~spl2_1 | ~spl2_2),
% 1.34/0.58    inference(avatar_split_clause,[],[f39,f63,f59])).
% 1.34/0.58  fof(f39,plain,(
% 1.34/0.58    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | ~v2_tops_1(sK1,sK0)),
% 1.34/0.58    inference(cnf_transformation,[],[f32])).
% 1.34/0.58  % SZS output end Proof for theBenchmark
% 1.34/0.58  % (31370)------------------------------
% 1.34/0.58  % (31370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.58  % (31370)Termination reason: Refutation
% 1.34/0.58  
% 1.34/0.58  % (31370)Memory used [KB]: 11385
% 1.34/0.58  % (31370)Time elapsed: 0.163 s
% 1.34/0.58  % (31370)------------------------------
% 1.34/0.58  % (31370)------------------------------
% 1.34/0.58  % (31359)Success in time 0.218 s
%------------------------------------------------------------------------------
