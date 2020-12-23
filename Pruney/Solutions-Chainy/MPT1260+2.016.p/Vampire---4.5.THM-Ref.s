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
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 24.91s
% Output     : Refutation 24.91s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 895 expanded)
%              Number of leaves         :   36 ( 255 expanded)
%              Depth                    :   23
%              Number of atoms          :  718 (4233 expanded)
%              Number of equality atoms :  148 (1158 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f155,f238,f242,f9324,f36038,f44112,f44155,f44256,f44492])).

fof(f44492,plain,
    ( spl4_2
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f44491])).

fof(f44491,plain,
    ( $false
    | spl4_2
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f44490,f153])).

fof(f153,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f44490,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f178,f346])).

fof(f346,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl4_21
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f178,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f158,f71])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).

fof(f53,plain,
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

fof(f54,plain,
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

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f28,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f158,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f44256,plain,
    ( ~ spl4_20
    | spl4_21 ),
    inference(avatar_split_clause,[],[f44254,f344,f340])).

fof(f340,plain,
    ( spl4_20
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f44254,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f334,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f334,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f331,f180])).

fof(f180,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f160,f71])).

fof(f160,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f331,plain,(
    ! [X6] : r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X6),sK1) ),
    inference(superposition,[],[f120,f162])).

fof(f162,plain,(
    ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1))) ),
    inference(resolution,[],[f72,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f103,f117])).

fof(f117,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f89,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f89,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f120,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f86,f117])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f44155,plain,
    ( spl4_20
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f44154,f147,f340])).

fof(f147,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44154,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f36344,f139])).

fof(f139,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f36344,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f167,f72])).

fof(f167,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f156,f71])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ v3_pre_topc(X0,sK0)
      | r1_tarski(X0,k1_tops_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f72,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f44112,plain,
    ( ~ spl4_2
    | ~ spl4_11
    | spl4_20 ),
    inference(avatar_contradiction_clause,[],[f44111])).

fof(f44111,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_11
    | spl4_20 ),
    inference(subsumption_resolution,[],[f44011,f139])).

fof(f44011,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl4_2
    | ~ spl4_11
    | spl4_20 ),
    inference(backward_demodulation,[],[f342,f43952])).

fof(f43952,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(backward_demodulation,[],[f348,f43919])).

fof(f43919,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f43865,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f114,f88])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f43865,plain,
    ( sK1 = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))
    | ~ r2_hidden(sK3(sK1,k1_tops_1(sK0,sK1),sK1),sK1)
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(resolution,[],[f43823,f5436])).

fof(f5436,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f5434,f1971])).

fof(f1971,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_tops_1(sK0,sK1))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl4_2
    | ~ spl4_11 ),
    inference(superposition,[],[f1872,f152])).

fof(f152,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f151])).

fof(f1872,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2))
        | ~ r2_hidden(X3,X2) )
    | ~ spl4_11 ),
    inference(superposition,[],[f141,f290])).

fof(f290,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X1)))
    | ~ spl4_11 ),
    inference(resolution,[],[f271,f125])).

fof(f271,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f270,f72])).

fof(f270,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f269,f237])).

fof(f237,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_11
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f269,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f104,f179])).

fof(f179,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f159,f71])).

fof(f159,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f141,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f106,f117])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).

fof(f63,plain,(
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

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f60])).

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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5434,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_tops_1(sK0,sK1))
      | r2_hidden(X2,k2_tops_1(sK0,sK1))
      | ~ r2_hidden(X2,sK1) ) ),
    inference(superposition,[],[f330,f180])).

fof(f330,plain,(
    ! [X4,X5] :
      ( r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4))
      | r2_hidden(X5,X4)
      | ~ r2_hidden(X5,sK1) ) ),
    inference(superposition,[],[f140,f162])).

fof(f140,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f107,f117])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f43823,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK1,X0,sK1),X0)
      | sK1 = k1_setfam_1(k2_tarski(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f43821,f134])).

fof(f43821,plain,(
    ! [X0] :
      ( sK1 = k1_setfam_1(k2_tarski(sK1,X0))
      | ~ r2_hidden(sK3(sK1,X0,sK1),X0)
      | ~ r2_hidden(sK3(sK1,X0,sK1),sK1) ) ),
    inference(duplicate_literal_removal,[],[f43820])).

fof(f43820,plain,(
    ! [X0] :
      ( sK1 = k1_setfam_1(k2_tarski(sK1,X0))
      | ~ r2_hidden(sK3(sK1,X0,sK1),X0)
      | ~ r2_hidden(sK3(sK1,X0,sK1),sK1)
      | sK1 = k1_setfam_1(k2_tarski(sK1,X0)) ) ),
    inference(resolution,[],[f43798,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f116,f88])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f43798,plain,(
    ! [X8] :
      ( r2_hidden(sK3(sK1,X8,sK1),sK1)
      | sK1 = k1_setfam_1(k2_tarski(sK1,X8)) ) ),
    inference(superposition,[],[f28762,f326])).

fof(f326,plain,(
    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(superposition,[],[f162,f119])).

fof(f119,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f76,f117])).

fof(f76,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f28762,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1,X0,k7_subset_1(u1_struct_0(sK0),sK1,X1)),sK1)
      | k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(sK1,X0)) ) ),
    inference(factoring,[],[f493])).

fof(f493,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK3(X6,X7,k7_subset_1(u1_struct_0(sK0),sK1,X8)),sK1)
      | r2_hidden(sK3(X6,X7,k7_subset_1(u1_struct_0(sK0),sK1,X8)),X6)
      | k1_setfam_1(k2_tarski(X6,X7)) = k7_subset_1(u1_struct_0(sK0),sK1,X8) ) ),
    inference(resolution,[],[f328,f134])).

fof(f328,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k7_subset_1(u1_struct_0(sK0),sK1,X0))
      | r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f142,f162])).

fof(f142,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f105,f117])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f348,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f338,f87])).

fof(f87,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f338,plain,(
    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f334,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f90,f88])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f342,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl4_20 ),
    inference(avatar_component_clause,[],[f340])).

fof(f36038,plain,
    ( ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(avatar_contradiction_clause,[],[f36037])).

fof(f36037,plain,
    ( $false
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f36036,f71])).

fof(f36036,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f36035,f385])).

fof(f385,plain,
    ( m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f210,f349])).

fof(f349,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(forward_demodulation,[],[f182,f184])).

fof(f184,plain,(
    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f163,f121])).

fof(f163,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f182,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f166,f87])).

fof(f166,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f72,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ) ),
    inference(definition_unfolding,[],[f92,f117])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f210,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl4_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f36035,plain,
    ( ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f36034,f70])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f36034,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f36033,f386])).

fof(f386,plain,
    ( ~ v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | spl4_8 ),
    inference(backward_demodulation,[],[f215,f349])).

fof(f215,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f213])).

fof(f213,plain,
    ( spl4_8
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f36033,plain,
    ( v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(trivial_inequality_removal,[],[f36032])).

fof(f36032,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1)
    | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(superposition,[],[f82,f36021])).

fof(f36021,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f1581,f25729])).

fof(f25729,plain,
    ( k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f25728,f349])).

fof(f25728,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_11
    | ~ spl4_21 ),
    inference(forward_demodulation,[],[f25712,f12172])).

fof(f12172,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_21 ),
    inference(backward_demodulation,[],[f180,f346])).

fof(f25712,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(resolution,[],[f251,f72])).

fof(f251,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,sK1)) )
    | ~ spl4_11 ),
    inference(resolution,[],[f237,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

fof(f1581,plain,
    ( k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f365,f349])).

fof(f365,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f364,f181])).

fof(f181,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f161,f71])).

fof(f161,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).

fof(f364,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f353,f71])).

fof(f353,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f210,f79])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

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
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f9324,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | spl4_1 ),
    inference(avatar_split_clause,[],[f7323,f147,f213,f209])).

fof(f7323,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f203,f71])).

fof(f203,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f83,f165])).

fof(f165,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f72,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f242,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f241])).

fof(f241,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f239,f72])).

fof(f239,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_7 ),
    inference(resolution,[],[f211,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f211,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f209])).

fof(f238,plain,
    ( ~ spl4_7
    | spl4_11 ),
    inference(avatar_split_clause,[],[f233,f235,f209])).

fof(f233,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f232,f71])).

fof(f232,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f95,f181])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f155,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f73,f151,f147])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f154,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f74,f151,f147])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (31981)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (31973)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (31963)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (31965)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31974)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (31960)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (31982)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (31966)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (31968)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (31971)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (31962)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (31983)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (31985)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (31961)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (31964)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (31976)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (31987)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (31975)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (31986)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (31979)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (31967)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (31988)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (31977)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (31978)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (31959)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.56  % (31969)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (31980)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.56  % (31970)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (31972)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (31984)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.57  % (31975)Refutation not found, incomplete strategy% (31975)------------------------------
% 0.22/0.57  % (31975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (31975)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (31975)Memory used [KB]: 10746
% 0.22/0.57  % (31975)Time elapsed: 0.138 s
% 0.22/0.57  % (31975)------------------------------
% 0.22/0.57  % (31975)------------------------------
% 0.22/0.59  % (31969)Refutation not found, incomplete strategy% (31969)------------------------------
% 0.22/0.59  % (31969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (31969)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (31969)Memory used [KB]: 11001
% 0.22/0.59  % (31969)Time elapsed: 0.181 s
% 0.22/0.59  % (31969)------------------------------
% 0.22/0.59  % (31969)------------------------------
% 2.64/0.72  % (31990)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.64/0.72  % (31991)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.13/0.82  % (31983)Time limit reached!
% 3.13/0.82  % (31983)------------------------------
% 3.13/0.82  % (31983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (31983)Termination reason: Time limit
% 3.13/0.82  % (31983)Termination phase: Saturation
% 3.13/0.82  
% 3.13/0.82  % (31983)Memory used [KB]: 14072
% 3.13/0.82  % (31983)Time elapsed: 0.400 s
% 3.13/0.82  % (31983)------------------------------
% 3.13/0.82  % (31983)------------------------------
% 3.13/0.82  % (31961)Time limit reached!
% 3.13/0.82  % (31961)------------------------------
% 3.13/0.82  % (31961)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.13/0.82  % (31961)Termination reason: Time limit
% 3.13/0.82  % (31961)Termination phase: Saturation
% 3.13/0.82  
% 3.13/0.82  % (31961)Memory used [KB]: 6652
% 3.13/0.82  % (31961)Time elapsed: 0.400 s
% 3.13/0.82  % (31961)------------------------------
% 3.13/0.82  % (31961)------------------------------
% 4.11/0.91  % (31988)Time limit reached!
% 4.11/0.91  % (31988)------------------------------
% 4.11/0.91  % (31988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.11/0.92  % (31988)Termination reason: Time limit
% 4.11/0.92  
% 4.11/0.92  % (31988)Memory used [KB]: 5373
% 4.11/0.92  % (31988)Time elapsed: 0.513 s
% 4.11/0.92  % (31988)------------------------------
% 4.11/0.92  % (31988)------------------------------
% 4.42/0.96  % (31993)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.42/0.96  % (31965)Time limit reached!
% 4.42/0.96  % (31965)------------------------------
% 4.42/0.96  % (31965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.96  % (31973)Time limit reached!
% 4.42/0.96  % (31973)------------------------------
% 4.42/0.96  % (31973)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.42/0.96  % (31973)Termination reason: Time limit
% 4.42/0.96  % (31973)Termination phase: Saturation
% 4.42/0.96  
% 4.42/0.96  % (31973)Memory used [KB]: 6396
% 4.42/0.96  % (31973)Time elapsed: 0.500 s
% 4.42/0.96  % (31973)------------------------------
% 4.42/0.96  % (31973)------------------------------
% 4.42/0.97  % (31992)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.42/0.98  % (31965)Termination reason: Time limit
% 4.42/0.98  
% 4.42/0.98  % (31965)Memory used [KB]: 15735
% 4.42/0.98  % (31965)Time elapsed: 0.517 s
% 4.42/0.98  % (31965)------------------------------
% 4.42/0.98  % (31965)------------------------------
% 4.92/1.03  % (31966)Time limit reached!
% 4.92/1.03  % (31966)------------------------------
% 4.92/1.03  % (31966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.92/1.03  % (31966)Termination reason: Time limit
% 4.92/1.03  
% 4.92/1.03  % (31966)Memory used [KB]: 6652
% 4.92/1.03  % (31966)Time elapsed: 0.616 s
% 4.92/1.03  % (31966)------------------------------
% 4.92/1.03  % (31966)------------------------------
% 4.92/1.05  % (31994)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.35/1.10  % (31995)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.35/1.11  % (31996)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.35/1.14  % (31997)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.59/1.23  % (31960)Time limit reached!
% 6.59/1.23  % (31960)------------------------------
% 6.59/1.23  % (31960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.88/1.24  % (31960)Termination reason: Time limit
% 6.88/1.24  
% 6.88/1.24  % (31960)Memory used [KB]: 9978
% 6.88/1.24  % (31960)Time elapsed: 0.814 s
% 6.88/1.24  % (31960)------------------------------
% 6.88/1.24  % (31960)------------------------------
% 6.88/1.32  % (31962)Time limit reached!
% 6.88/1.32  % (31962)------------------------------
% 6.88/1.32  % (31962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.88/1.32  % (31962)Termination reason: Time limit
% 6.88/1.32  
% 6.88/1.32  % (31962)Memory used [KB]: 7419
% 6.88/1.32  % (31962)Time elapsed: 0.905 s
% 6.88/1.32  % (31962)------------------------------
% 6.88/1.32  % (31962)------------------------------
% 7.61/1.34  % (31998)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.02/1.41  % (31986)Time limit reached!
% 8.02/1.41  % (31986)------------------------------
% 8.02/1.41  % (31986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.41  % (31986)Termination reason: Time limit
% 8.02/1.41  % (31986)Termination phase: Saturation
% 8.02/1.41  
% 8.02/1.41  % (31986)Memory used [KB]: 13688
% 8.02/1.41  % (31986)Time elapsed: 1.0000 s
% 8.02/1.41  % (31986)------------------------------
% 8.02/1.41  % (31986)------------------------------
% 8.02/1.41  % (31971)Time limit reached!
% 8.02/1.41  % (31971)------------------------------
% 8.02/1.41  % (31971)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.02/1.41  % (31971)Termination reason: Time limit
% 8.02/1.41  % (31971)Termination phase: Saturation
% 8.02/1.41  
% 8.02/1.41  % (31971)Memory used [KB]: 17270
% 8.02/1.41  % (31971)Time elapsed: 1.013 s
% 8.02/1.41  % (31971)------------------------------
% 8.02/1.41  % (31971)------------------------------
% 8.49/1.45  % (31999)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.85/1.50  % (32000)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.85/1.54  % (32001)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.12/1.62  % (31959)Time limit reached!
% 9.12/1.62  % (31959)------------------------------
% 9.12/1.62  % (31959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.12/1.62  % (31959)Termination reason: Time limit
% 9.12/1.62  
% 9.12/1.62  % (31959)Memory used [KB]: 3454
% 9.12/1.62  % (31959)Time elapsed: 1.206 s
% 9.12/1.62  % (31959)------------------------------
% 9.12/1.62  % (31959)------------------------------
% 9.12/1.62  % (31996)Time limit reached!
% 9.12/1.62  % (31996)------------------------------
% 9.12/1.62  % (31996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.12/1.62  % (31996)Termination reason: Time limit
% 9.12/1.62  % (31996)Termination phase: Saturation
% 9.12/1.62  
% 9.12/1.62  % (31996)Memory used [KB]: 17654
% 9.12/1.62  % (31996)Time elapsed: 0.600 s
% 9.12/1.62  % (31996)------------------------------
% 9.12/1.62  % (31996)------------------------------
% 9.77/1.66  % (31992)Time limit reached!
% 9.77/1.66  % (31992)------------------------------
% 9.77/1.66  % (31992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.77/1.66  % (31992)Termination reason: Time limit
% 9.77/1.66  
% 9.77/1.66  % (31992)Memory used [KB]: 8955
% 9.77/1.66  % (31992)Time elapsed: 0.821 s
% 9.77/1.66  % (31992)------------------------------
% 9.77/1.66  % (31992)------------------------------
% 10.13/1.72  % (31964)Time limit reached!
% 10.13/1.72  % (31964)------------------------------
% 10.13/1.72  % (31964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.13/1.72  % (31964)Termination reason: Time limit
% 10.13/1.72  
% 10.13/1.72  % (31964)Memory used [KB]: 14456
% 10.13/1.72  % (31964)Time elapsed: 1.309 s
% 10.13/1.72  % (31964)------------------------------
% 10.13/1.72  % (31964)------------------------------
% 10.13/1.75  % (32002)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.13/1.77  % (32003)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.11/1.79  % (32004)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.69/1.87  % (32005)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 12.30/1.93  % (32004)Refutation not found, incomplete strategy% (32004)------------------------------
% 12.30/1.93  % (32004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.30/1.93  % (32004)Termination reason: Refutation not found, incomplete strategy
% 12.30/1.93  
% 12.30/1.93  % (32004)Memory used [KB]: 6396
% 12.30/1.93  % (32004)Time elapsed: 0.222 s
% 12.30/1.93  % (32004)------------------------------
% 12.30/1.93  % (32004)------------------------------
% 12.71/2.03  % (31985)Time limit reached!
% 12.71/2.03  % (31985)------------------------------
% 12.71/2.03  % (31985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.71/2.03  % (31985)Termination reason: Time limit
% 12.71/2.03  
% 12.71/2.03  % (31985)Memory used [KB]: 15351
% 12.71/2.03  % (31985)Time elapsed: 1.624 s
% 12.71/2.03  % (31985)------------------------------
% 12.71/2.03  % (31985)------------------------------
% 12.71/2.04  % (32003)Time limit reached!
% 12.71/2.04  % (32003)------------------------------
% 12.71/2.04  % (32003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.34/2.06  % (32003)Termination reason: Time limit
% 13.34/2.06  % (32003)Termination phase: Saturation
% 13.34/2.06  
% 13.34/2.06  % (32003)Memory used [KB]: 14967
% 13.34/2.06  % (32003)Time elapsed: 0.400 s
% 13.34/2.06  % (32003)------------------------------
% 13.34/2.06  % (32003)------------------------------
% 13.34/2.06  % (32006)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 13.96/2.15  % (32007)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 13.96/2.15  % (31999)Time limit reached!
% 13.96/2.15  % (31999)------------------------------
% 13.96/2.15  % (31999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.96/2.15  % (31999)Termination reason: Time limit
% 13.96/2.15  
% 13.96/2.15  % (31999)Memory used [KB]: 17526
% 13.96/2.15  % (31999)Time elapsed: 0.812 s
% 13.96/2.15  % (31999)------------------------------
% 13.96/2.15  % (31999)------------------------------
% 13.96/2.17  % (32005)Time limit reached!
% 13.96/2.17  % (32005)------------------------------
% 13.96/2.17  % (32005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.96/2.17  % (32005)Termination reason: Time limit
% 13.96/2.17  
% 13.96/2.17  % (32005)Memory used [KB]: 6780
% 13.96/2.17  % (32005)Time elapsed: 0.406 s
% 13.96/2.17  % (32005)------------------------------
% 13.96/2.17  % (32005)------------------------------
% 13.96/2.18  % (32008)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 14.56/2.22  % (31979)Time limit reached!
% 14.56/2.22  % (31979)------------------------------
% 14.56/2.22  % (31979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.56/2.22  % (31979)Termination reason: Time limit
% 14.56/2.22  % (31979)Termination phase: Saturation
% 14.56/2.22  
% 14.56/2.22  % (31979)Memory used [KB]: 24434
% 14.56/2.22  % (31979)Time elapsed: 1.812 s
% 14.56/2.22  % (31979)------------------------------
% 14.56/2.22  % (31979)------------------------------
% 14.56/2.27  % (32010)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 14.56/2.29  % (32009)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 16.32/2.47  % (32006)Time limit reached!
% 16.32/2.47  % (32006)------------------------------
% 16.32/2.47  % (32006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.32/2.47  % (32006)Termination reason: Time limit
% 16.32/2.47  
% 16.32/2.47  % (32006)Memory used [KB]: 11897
% 16.32/2.47  % (32006)Time elapsed: 0.519 s
% 16.32/2.47  % (32006)------------------------------
% 16.32/2.47  % (32006)------------------------------
% 16.32/2.47  % (32007)Time limit reached!
% 16.32/2.47  % (32007)------------------------------
% 16.32/2.47  % (32007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.32/2.48  % (32007)Termination reason: Time limit
% 16.32/2.48  
% 16.32/2.48  % (32007)Memory used [KB]: 9594
% 16.32/2.48  % (32007)Time elapsed: 0.408 s
% 16.32/2.48  % (32007)------------------------------
% 16.32/2.48  % (32007)------------------------------
% 17.55/2.58  % (32010)Time limit reached!
% 17.55/2.58  % (32010)------------------------------
% 17.55/2.58  % (32010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.55/2.59  % (32009)Time limit reached!
% 17.55/2.59  % (32009)------------------------------
% 17.55/2.59  % (32009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.55/2.60  % (32010)Termination reason: Time limit
% 17.55/2.60  % (32010)Termination phase: Saturation
% 17.55/2.60  
% 17.55/2.60  % (32010)Memory used [KB]: 7036
% 17.55/2.60  % (32010)Time elapsed: 0.400 s
% 17.55/2.60  % (32010)------------------------------
% 17.55/2.60  % (32010)------------------------------
% 17.55/2.60  % (32009)Termination reason: Time limit
% 17.55/2.60  % (32009)Termination phase: Saturation
% 17.55/2.60  
% 17.55/2.60  % (32009)Memory used [KB]: 4093
% 17.55/2.60  % (32009)Time elapsed: 0.400 s
% 17.55/2.60  % (32009)------------------------------
% 17.55/2.60  % (32009)------------------------------
% 18.78/2.81  % (31974)Time limit reached!
% 18.78/2.81  % (31974)------------------------------
% 18.78/2.81  % (31974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.46/2.83  % (31974)Termination reason: Time limit
% 19.46/2.83  % (31974)Termination phase: Saturation
% 19.46/2.83  
% 19.46/2.83  % (31974)Memory used [KB]: 11641
% 19.46/2.83  % (31974)Time elapsed: 2.400 s
% 19.46/2.83  % (31974)------------------------------
% 19.46/2.83  % (31974)------------------------------
% 24.91/3.55  % (31994)Refutation found. Thanks to Tanya!
% 24.91/3.55  % SZS status Theorem for theBenchmark
% 24.91/3.56  % SZS output start Proof for theBenchmark
% 24.91/3.56  fof(f44493,plain,(
% 24.91/3.56    $false),
% 24.91/3.56    inference(avatar_sat_refutation,[],[f154,f155,f238,f242,f9324,f36038,f44112,f44155,f44256,f44492])).
% 24.91/3.56  fof(f44492,plain,(
% 24.91/3.56    spl4_2 | ~spl4_21),
% 24.91/3.56    inference(avatar_contradiction_clause,[],[f44491])).
% 24.91/3.56  fof(f44491,plain,(
% 24.91/3.56    $false | (spl4_2 | ~spl4_21)),
% 24.91/3.56    inference(subsumption_resolution,[],[f44490,f153])).
% 24.91/3.56  fof(f153,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 24.91/3.56    inference(avatar_component_clause,[],[f151])).
% 24.91/3.56  fof(f151,plain,(
% 24.91/3.56    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 24.91/3.56  fof(f44490,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_21),
% 24.91/3.56    inference(forward_demodulation,[],[f178,f346])).
% 24.91/3.56  fof(f346,plain,(
% 24.91/3.56    sK1 = k1_tops_1(sK0,sK1) | ~spl4_21),
% 24.91/3.56    inference(avatar_component_clause,[],[f344])).
% 24.91/3.56  fof(f344,plain,(
% 24.91/3.56    spl4_21 <=> sK1 = k1_tops_1(sK0,sK1)),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 24.91/3.56  fof(f178,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 24.91/3.56    inference(subsumption_resolution,[],[f158,f71])).
% 24.91/3.56  fof(f71,plain,(
% 24.91/3.56    l1_pre_topc(sK0)),
% 24.91/3.56    inference(cnf_transformation,[],[f55])).
% 24.91/3.56  fof(f55,plain,(
% 24.91/3.56    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 24.91/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f52,f54,f53])).
% 24.91/3.56  fof(f53,plain,(
% 24.91/3.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 24.91/3.56    introduced(choice_axiom,[])).
% 24.91/3.56  fof(f54,plain,(
% 24.91/3.56    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 24.91/3.56    introduced(choice_axiom,[])).
% 24.91/3.56  fof(f52,plain,(
% 24.91/3.56    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.91/3.56    inference(flattening,[],[f51])).
% 24.91/3.56  fof(f51,plain,(
% 24.91/3.56    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.91/3.56    inference(nnf_transformation,[],[f31])).
% 24.91/3.56  fof(f31,plain,(
% 24.91/3.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 24.91/3.56    inference(flattening,[],[f30])).
% 24.91/3.56  fof(f30,plain,(
% 24.91/3.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f29])).
% 24.91/3.56  fof(f29,negated_conjecture,(
% 24.91/3.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 24.91/3.56    inference(negated_conjecture,[],[f28])).
% 24.91/3.56  fof(f28,conjecture,(
% 24.91/3.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 24.91/3.56  fof(f158,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(resolution,[],[f72,f80])).
% 24.91/3.56  fof(f80,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f35])).
% 24.91/3.56  fof(f35,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f22])).
% 24.91/3.56  fof(f22,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 24.91/3.56  fof(f72,plain,(
% 24.91/3.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    inference(cnf_transformation,[],[f55])).
% 24.91/3.56  fof(f44256,plain,(
% 24.91/3.56    ~spl4_20 | spl4_21),
% 24.91/3.56    inference(avatar_split_clause,[],[f44254,f344,f340])).
% 24.91/3.56  fof(f340,plain,(
% 24.91/3.56    spl4_20 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 24.91/3.56  fof(f44254,plain,(
% 24.91/3.56    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 24.91/3.56    inference(resolution,[],[f334,f98])).
% 24.91/3.56  fof(f98,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f58])).
% 24.91/3.56  fof(f58,plain,(
% 24.91/3.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 24.91/3.56    inference(flattening,[],[f57])).
% 24.91/3.56  fof(f57,plain,(
% 24.91/3.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 24.91/3.56    inference(nnf_transformation,[],[f3])).
% 24.91/3.56  fof(f3,axiom,(
% 24.91/3.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 24.91/3.56  fof(f334,plain,(
% 24.91/3.56    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 24.91/3.56    inference(superposition,[],[f331,f180])).
% 24.91/3.56  fof(f180,plain,(
% 24.91/3.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 24.91/3.56    inference(subsumption_resolution,[],[f160,f71])).
% 24.91/3.56  fof(f160,plain,(
% 24.91/3.56    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(resolution,[],[f72,f78])).
% 24.91/3.56  fof(f78,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f33])).
% 24.91/3.56  fof(f33,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f27])).
% 24.91/3.56  fof(f27,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 24.91/3.56  fof(f331,plain,(
% 24.91/3.56    ( ! [X6] : (r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,X6),sK1)) )),
% 24.91/3.56    inference(superposition,[],[f120,f162])).
% 24.91/3.56  fof(f162,plain,(
% 24.91/3.56    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k5_xboole_0(sK1,k1_setfam_1(k2_tarski(sK1,X1)))) )),
% 24.91/3.56    inference(resolution,[],[f72,f125])).
% 24.91/3.56  fof(f125,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) )),
% 24.91/3.56    inference(definition_unfolding,[],[f103,f117])).
% 24.91/3.56  fof(f117,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 24.91/3.56    inference(definition_unfolding,[],[f89,f88])).
% 24.91/3.56  fof(f88,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f18])).
% 24.91/3.56  fof(f18,axiom,(
% 24.91/3.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 24.91/3.56  fof(f89,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f4])).
% 24.91/3.56  fof(f4,axiom,(
% 24.91/3.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 24.91/3.56  fof(f103,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f48])).
% 24.91/3.56  fof(f48,plain,(
% 24.91/3.56    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f16])).
% 24.91/3.56  fof(f16,axiom,(
% 24.91/3.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 24.91/3.56  fof(f120,plain,(
% 24.91/3.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 24.91/3.56    inference(definition_unfolding,[],[f86,f117])).
% 24.91/3.56  fof(f86,plain,(
% 24.91/3.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f8])).
% 24.91/3.56  fof(f8,axiom,(
% 24.91/3.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 24.91/3.56  fof(f44155,plain,(
% 24.91/3.56    spl4_20 | ~spl4_1),
% 24.91/3.56    inference(avatar_split_clause,[],[f44154,f147,f340])).
% 24.91/3.56  fof(f147,plain,(
% 24.91/3.56    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 24.91/3.56  fof(f44154,plain,(
% 24.91/3.56    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 24.91/3.56    inference(subsumption_resolution,[],[f36344,f139])).
% 24.91/3.56  fof(f139,plain,(
% 24.91/3.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 24.91/3.56    inference(equality_resolution,[],[f96])).
% 24.91/3.56  fof(f96,plain,(
% 24.91/3.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 24.91/3.56    inference(cnf_transformation,[],[f58])).
% 24.91/3.56  fof(f36344,plain,(
% 24.91/3.56    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1)),
% 24.91/3.56    inference(resolution,[],[f167,f72])).
% 24.91/3.56  fof(f167,plain,(
% 24.91/3.56    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1)) )),
% 24.91/3.56    inference(subsumption_resolution,[],[f156,f71])).
% 24.91/3.56  fof(f156,plain,(
% 24.91/3.56    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 24.91/3.56    inference(resolution,[],[f72,f85])).
% 24.91/3.56  fof(f85,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f40])).
% 24.91/3.56  fof(f40,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(flattening,[],[f39])).
% 24.91/3.56  fof(f39,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f24])).
% 24.91/3.56  fof(f24,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 24.91/3.56  fof(f44112,plain,(
% 24.91/3.56    ~spl4_2 | ~spl4_11 | spl4_20),
% 24.91/3.56    inference(avatar_contradiction_clause,[],[f44111])).
% 24.91/3.56  fof(f44111,plain,(
% 24.91/3.56    $false | (~spl4_2 | ~spl4_11 | spl4_20)),
% 24.91/3.56    inference(subsumption_resolution,[],[f44011,f139])).
% 24.91/3.56  fof(f44011,plain,(
% 24.91/3.56    ~r1_tarski(sK1,sK1) | (~spl4_2 | ~spl4_11 | spl4_20)),
% 24.91/3.56    inference(backward_demodulation,[],[f342,f43952])).
% 24.91/3.56  fof(f43952,plain,(
% 24.91/3.56    sK1 = k1_tops_1(sK0,sK1) | (~spl4_2 | ~spl4_11)),
% 24.91/3.56    inference(backward_demodulation,[],[f348,f43919])).
% 24.91/3.56  fof(f43919,plain,(
% 24.91/3.56    sK1 = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | (~spl4_2 | ~spl4_11)),
% 24.91/3.56    inference(subsumption_resolution,[],[f43865,f134])).
% 24.91/3.56  fof(f134,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 24.91/3.56    inference(definition_unfolding,[],[f114,f88])).
% 24.91/3.56  fof(f114,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f69])).
% 24.91/3.56  fof(f69,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f67,f68])).
% 24.91/3.56  fof(f68,plain,(
% 24.91/3.56    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 24.91/3.56    introduced(choice_axiom,[])).
% 24.91/3.56  fof(f67,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(rectify,[],[f66])).
% 24.91/3.56  fof(f66,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(flattening,[],[f65])).
% 24.91/3.56  fof(f65,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(nnf_transformation,[],[f1])).
% 24.91/3.56  fof(f1,axiom,(
% 24.91/3.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 24.91/3.56  fof(f43865,plain,(
% 24.91/3.56    sK1 = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1))) | ~r2_hidden(sK3(sK1,k1_tops_1(sK0,sK1),sK1),sK1) | (~spl4_2 | ~spl4_11)),
% 24.91/3.56    inference(resolution,[],[f43823,f5436])).
% 24.91/3.56  fof(f5436,plain,(
% 24.91/3.56    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) ) | (~spl4_2 | ~spl4_11)),
% 24.91/3.56    inference(subsumption_resolution,[],[f5434,f1971])).
% 24.91/3.56  fof(f1971,plain,(
% 24.91/3.56    ( ! [X3] : (~r2_hidden(X3,k2_tops_1(sK0,sK1)) | ~r2_hidden(X3,sK1)) ) | (~spl4_2 | ~spl4_11)),
% 24.91/3.56    inference(superposition,[],[f1872,f152])).
% 24.91/3.56  fof(f152,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 24.91/3.56    inference(avatar_component_clause,[],[f151])).
% 24.91/3.56  fof(f1872,plain,(
% 24.91/3.56    ( ! [X2,X3] : (~r2_hidden(X3,k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X2)) | ~r2_hidden(X3,X2)) ) | ~spl4_11),
% 24.91/3.56    inference(superposition,[],[f141,f290])).
% 24.91/3.56  fof(f290,plain,(
% 24.91/3.56    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k5_xboole_0(k2_pre_topc(sK0,sK1),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),X1)))) ) | ~spl4_11),
% 24.91/3.56    inference(resolution,[],[f271,f125])).
% 24.91/3.56  fof(f271,plain,(
% 24.91/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_11),
% 24.91/3.56    inference(subsumption_resolution,[],[f270,f72])).
% 24.91/3.56  fof(f270,plain,(
% 24.91/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_11),
% 24.91/3.56    inference(subsumption_resolution,[],[f269,f237])).
% 24.91/3.56  fof(f237,plain,(
% 24.91/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_11),
% 24.91/3.56    inference(avatar_component_clause,[],[f235])).
% 24.91/3.56  fof(f235,plain,(
% 24.91/3.56    spl4_11 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 24.91/3.56  fof(f269,plain,(
% 24.91/3.56    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    inference(superposition,[],[f104,f179])).
% 24.91/3.56  fof(f179,plain,(
% 24.91/3.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 24.91/3.56    inference(subsumption_resolution,[],[f159,f71])).
% 24.91/3.56  fof(f159,plain,(
% 24.91/3.56    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(resolution,[],[f72,f79])).
% 24.91/3.56  fof(f79,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f34])).
% 24.91/3.56  fof(f34,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f26])).
% 24.91/3.56  fof(f26,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 24.91/3.56  fof(f104,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f50])).
% 24.91/3.56  fof(f50,plain,(
% 24.91/3.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(flattening,[],[f49])).
% 24.91/3.56  fof(f49,plain,(
% 24.91/3.56    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 24.91/3.56    inference(ennf_transformation,[],[f14])).
% 24.91/3.56  fof(f14,axiom,(
% 24.91/3.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 24.91/3.56  fof(f141,plain,(
% 24.91/3.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | ~r2_hidden(X4,X1)) )),
% 24.91/3.56    inference(equality_resolution,[],[f130])).
% 24.91/3.56  fof(f130,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 24.91/3.56    inference(definition_unfolding,[],[f106,f117])).
% 24.91/3.56  fof(f106,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 24.91/3.56    inference(cnf_transformation,[],[f64])).
% 24.91/3.56  fof(f64,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f62,f63])).
% 24.91/3.56  fof(f63,plain,(
% 24.91/3.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((~r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 24.91/3.56    introduced(choice_axiom,[])).
% 24.91/3.56  fof(f62,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(rectify,[],[f61])).
% 24.91/3.56  fof(f61,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(flattening,[],[f60])).
% 24.91/3.56  fof(f60,plain,(
% 24.91/3.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 24.91/3.56    inference(nnf_transformation,[],[f2])).
% 24.91/3.56  fof(f2,axiom,(
% 24.91/3.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 24.91/3.56  fof(f5434,plain,(
% 24.91/3.56    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | r2_hidden(X2,k2_tops_1(sK0,sK1)) | ~r2_hidden(X2,sK1)) )),
% 24.91/3.56    inference(superposition,[],[f330,f180])).
% 24.91/3.56  fof(f330,plain,(
% 24.91/3.56    ( ! [X4,X5] : (r2_hidden(X5,k7_subset_1(u1_struct_0(sK0),sK1,X4)) | r2_hidden(X5,X4) | ~r2_hidden(X5,sK1)) )),
% 24.91/3.56    inference(superposition,[],[f140,f162])).
% 24.91/3.56  fof(f140,plain,(
% 24.91/3.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 24.91/3.56    inference(equality_resolution,[],[f129])).
% 24.91/3.56  fof(f129,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 24.91/3.56    inference(definition_unfolding,[],[f107,f117])).
% 24.91/3.56  fof(f107,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 24.91/3.56    inference(cnf_transformation,[],[f64])).
% 24.91/3.56  fof(f43823,plain,(
% 24.91/3.56    ( ! [X0] : (~r2_hidden(sK3(sK1,X0,sK1),X0) | sK1 = k1_setfam_1(k2_tarski(sK1,X0))) )),
% 24.91/3.56    inference(subsumption_resolution,[],[f43821,f134])).
% 24.91/3.56  fof(f43821,plain,(
% 24.91/3.56    ( ! [X0] : (sK1 = k1_setfam_1(k2_tarski(sK1,X0)) | ~r2_hidden(sK3(sK1,X0,sK1),X0) | ~r2_hidden(sK3(sK1,X0,sK1),sK1)) )),
% 24.91/3.56    inference(duplicate_literal_removal,[],[f43820])).
% 24.91/3.56  fof(f43820,plain,(
% 24.91/3.56    ( ! [X0] : (sK1 = k1_setfam_1(k2_tarski(sK1,X0)) | ~r2_hidden(sK3(sK1,X0,sK1),X0) | ~r2_hidden(sK3(sK1,X0,sK1),sK1) | sK1 = k1_setfam_1(k2_tarski(sK1,X0))) )),
% 24.91/3.56    inference(resolution,[],[f43798,f132])).
% 24.91/3.56  fof(f132,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 24.91/3.56    inference(definition_unfolding,[],[f116,f88])).
% 24.91/3.56  fof(f116,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f69])).
% 24.91/3.56  fof(f43798,plain,(
% 24.91/3.56    ( ! [X8] : (r2_hidden(sK3(sK1,X8,sK1),sK1) | sK1 = k1_setfam_1(k2_tarski(sK1,X8))) )),
% 24.91/3.56    inference(superposition,[],[f28762,f326])).
% 24.91/3.56  fof(f326,plain,(
% 24.91/3.56    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)),
% 24.91/3.56    inference(superposition,[],[f162,f119])).
% 24.91/3.56  fof(f119,plain,(
% 24.91/3.56    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 24.91/3.56    inference(definition_unfolding,[],[f76,f117])).
% 24.91/3.56  fof(f76,plain,(
% 24.91/3.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 24.91/3.56    inference(cnf_transformation,[],[f9])).
% 24.91/3.56  fof(f9,axiom,(
% 24.91/3.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 24.91/3.56  fof(f28762,plain,(
% 24.91/3.56    ( ! [X0,X1] : (r2_hidden(sK3(sK1,X0,k7_subset_1(u1_struct_0(sK0),sK1,X1)),sK1) | k7_subset_1(u1_struct_0(sK0),sK1,X1) = k1_setfam_1(k2_tarski(sK1,X0))) )),
% 24.91/3.56    inference(factoring,[],[f493])).
% 24.91/3.56  fof(f493,plain,(
% 24.91/3.56    ( ! [X6,X8,X7] : (r2_hidden(sK3(X6,X7,k7_subset_1(u1_struct_0(sK0),sK1,X8)),sK1) | r2_hidden(sK3(X6,X7,k7_subset_1(u1_struct_0(sK0),sK1,X8)),X6) | k1_setfam_1(k2_tarski(X6,X7)) = k7_subset_1(u1_struct_0(sK0),sK1,X8)) )),
% 24.91/3.56    inference(resolution,[],[f328,f134])).
% 24.91/3.56  fof(f328,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~r2_hidden(X1,k7_subset_1(u1_struct_0(sK0),sK1,X0)) | r2_hidden(X1,sK1)) )),
% 24.91/3.56    inference(superposition,[],[f142,f162])).
% 24.91/3.56  fof(f142,plain,(
% 24.91/3.56    ( ! [X4,X0,X1] : (~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) | r2_hidden(X4,X0)) )),
% 24.91/3.56    inference(equality_resolution,[],[f131])).
% 24.91/3.56  fof(f131,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) != X2) )),
% 24.91/3.56    inference(definition_unfolding,[],[f105,f117])).
% 24.91/3.56  fof(f105,plain,(
% 24.91/3.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 24.91/3.56    inference(cnf_transformation,[],[f64])).
% 24.91/3.56  fof(f348,plain,(
% 24.91/3.56    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(sK1,k1_tops_1(sK0,sK1)))),
% 24.91/3.56    inference(forward_demodulation,[],[f338,f87])).
% 24.91/3.56  fof(f87,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f11])).
% 24.91/3.56  fof(f11,axiom,(
% 24.91/3.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 24.91/3.56  fof(f338,plain,(
% 24.91/3.56    k1_tops_1(sK0,sK1) = k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1))),
% 24.91/3.56    inference(resolution,[],[f334,f121])).
% 24.91/3.56  fof(f121,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 24.91/3.56    inference(definition_unfolding,[],[f90,f88])).
% 24.91/3.56  fof(f90,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f41])).
% 24.91/3.56  fof(f41,plain,(
% 24.91/3.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 24.91/3.56    inference(ennf_transformation,[],[f6])).
% 24.91/3.56  fof(f6,axiom,(
% 24.91/3.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 24.91/3.56  fof(f342,plain,(
% 24.91/3.56    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl4_20),
% 24.91/3.56    inference(avatar_component_clause,[],[f340])).
% 24.91/3.56  fof(f36038,plain,(
% 24.91/3.56    ~spl4_7 | spl4_8 | ~spl4_11 | ~spl4_21),
% 24.91/3.56    inference(avatar_contradiction_clause,[],[f36037])).
% 24.91/3.56  fof(f36037,plain,(
% 24.91/3.56    $false | (~spl4_7 | spl4_8 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(subsumption_resolution,[],[f36036,f71])).
% 24.91/3.56  fof(f36036,plain,(
% 24.91/3.56    ~l1_pre_topc(sK0) | (~spl4_7 | spl4_8 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(subsumption_resolution,[],[f36035,f385])).
% 24.91/3.56  fof(f385,plain,(
% 24.91/3.56    m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 24.91/3.56    inference(backward_demodulation,[],[f210,f349])).
% 24.91/3.56  fof(f349,plain,(
% 24.91/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),sK1)),
% 24.91/3.56    inference(forward_demodulation,[],[f182,f184])).
% 24.91/3.56  fof(f184,plain,(
% 24.91/3.56    sK1 = k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0)))),
% 24.91/3.56    inference(resolution,[],[f163,f121])).
% 24.91/3.56  fof(f163,plain,(
% 24.91/3.56    r1_tarski(sK1,u1_struct_0(sK0))),
% 24.91/3.56    inference(resolution,[],[f72,f99])).
% 24.91/3.56  fof(f99,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f59])).
% 24.91/3.56  fof(f59,plain,(
% 24.91/3.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 24.91/3.56    inference(nnf_transformation,[],[f19])).
% 24.91/3.56  fof(f19,axiom,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 24.91/3.56  fof(f182,plain,(
% 24.91/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(sK1,u1_struct_0(sK0))))),
% 24.91/3.56    inference(forward_demodulation,[],[f166,f87])).
% 24.91/3.56  fof(f166,plain,(
% 24.91/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k5_xboole_0(u1_struct_0(sK0),k1_setfam_1(k2_tarski(u1_struct_0(sK0),sK1)))),
% 24.91/3.56    inference(resolution,[],[f72,f122])).
% 24.91/3.56  fof(f122,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 24.91/3.56    inference(definition_unfolding,[],[f92,f117])).
% 24.91/3.56  fof(f92,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f43])).
% 24.91/3.56  fof(f43,plain,(
% 24.91/3.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f12])).
% 24.91/3.56  fof(f12,axiom,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 24.91/3.56  fof(f210,plain,(
% 24.91/3.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 24.91/3.56    inference(avatar_component_clause,[],[f209])).
% 24.91/3.56  fof(f209,plain,(
% 24.91/3.56    spl4_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 24.91/3.56  fof(f36035,plain,(
% 24.91/3.56    ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_7 | spl4_8 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(subsumption_resolution,[],[f36034,f70])).
% 24.91/3.56  fof(f70,plain,(
% 24.91/3.56    v2_pre_topc(sK0)),
% 24.91/3.56    inference(cnf_transformation,[],[f55])).
% 24.91/3.56  fof(f36034,plain,(
% 24.91/3.56    ~v2_pre_topc(sK0) | ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_7 | spl4_8 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(subsumption_resolution,[],[f36033,f386])).
% 24.91/3.56  fof(f386,plain,(
% 24.91/3.56    ~v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | spl4_8),
% 24.91/3.56    inference(backward_demodulation,[],[f215,f349])).
% 24.91/3.56  fof(f215,plain,(
% 24.91/3.56    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl4_8),
% 24.91/3.56    inference(avatar_component_clause,[],[f213])).
% 24.91/3.56  fof(f213,plain,(
% 24.91/3.56    spl4_8 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 24.91/3.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 24.91/3.56  fof(f36033,plain,(
% 24.91/3.56    v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_7 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(trivial_inequality_removal,[],[f36032])).
% 24.91/3.56  fof(f36032,plain,(
% 24.91/3.56    k5_xboole_0(u1_struct_0(sK0),sK1) != k5_xboole_0(u1_struct_0(sK0),sK1) | v4_pre_topc(k5_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~v2_pre_topc(sK0) | ~m1_subset_1(k5_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl4_7 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(superposition,[],[f82,f36021])).
% 24.91/3.56  fof(f36021,plain,(
% 24.91/3.56    k5_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) | (~spl4_7 | ~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(backward_demodulation,[],[f1581,f25729])).
% 24.91/3.56  fof(f25729,plain,(
% 24.91/3.56    k5_xboole_0(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(forward_demodulation,[],[f25728,f349])).
% 24.91/3.56  fof(f25728,plain,(
% 24.91/3.56    k3_subset_1(u1_struct_0(sK0),sK1) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl4_11 | ~spl4_21)),
% 24.91/3.56    inference(forward_demodulation,[],[f25712,f12172])).
% 24.91/3.56  fof(f12172,plain,(
% 24.91/3.56    sK1 = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl4_21),
% 24.91/3.56    inference(backward_demodulation,[],[f180,f346])).
% 24.91/3.56  fof(f25712,plain,(
% 24.91/3.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) | ~spl4_11),
% 24.91/3.56    inference(resolution,[],[f251,f72])).
% 24.91/3.56  fof(f251,plain,(
% 24.91/3.56    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X2),k2_tops_1(sK0,sK1))) ) | ~spl4_11),
% 24.91/3.56    inference(resolution,[],[f237,f94])).
% 24.91/3.56  fof(f94,plain,(
% 24.91/3.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f45])).
% 24.91/3.56  fof(f45,plain,(
% 24.91/3.56    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f17])).
% 24.91/3.56  fof(f17,axiom,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).
% 24.91/3.56  fof(f1581,plain,(
% 24.91/3.56    k2_pre_topc(sK0,k5_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k5_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl4_7),
% 24.91/3.56    inference(forward_demodulation,[],[f365,f349])).
% 24.91/3.56  fof(f365,plain,(
% 24.91/3.56    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl4_7),
% 24.91/3.56    inference(forward_demodulation,[],[f364,f181])).
% 24.91/3.56  fof(f181,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 24.91/3.56    inference(subsumption_resolution,[],[f161,f71])).
% 24.91/3.56  fof(f161,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(resolution,[],[f72,f77])).
% 24.91/3.56  fof(f77,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f32])).
% 24.91/3.56  fof(f32,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f25])).
% 24.91/3.56  fof(f25,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_1)).
% 24.91/3.56  fof(f364,plain,(
% 24.91/3.56    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl4_7),
% 24.91/3.56    inference(subsumption_resolution,[],[f353,f71])).
% 24.91/3.56  fof(f353,plain,(
% 24.91/3.56    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~spl4_7),
% 24.91/3.56    inference(resolution,[],[f210,f79])).
% 24.91/3.56  fof(f82,plain,(
% 24.91/3.56    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != X1 | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f37])).
% 24.91/3.56  fof(f37,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(flattening,[],[f36])).
% 24.91/3.56  fof(f36,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f20])).
% 24.91/3.56  fof(f20,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 24.91/3.56  fof(f9324,plain,(
% 24.91/3.56    ~spl4_7 | ~spl4_8 | spl4_1),
% 24.91/3.56    inference(avatar_split_clause,[],[f7323,f147,f213,f209])).
% 24.91/3.56  fof(f7323,plain,(
% 24.91/3.56    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    inference(subsumption_resolution,[],[f203,f71])).
% 24.91/3.56  fof(f203,plain,(
% 24.91/3.56    v3_pre_topc(sK1,sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(superposition,[],[f83,f165])).
% 24.91/3.56  fof(f165,plain,(
% 24.91/3.56    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 24.91/3.56    inference(resolution,[],[f72,f93])).
% 24.91/3.56  fof(f93,plain,(
% 24.91/3.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 24.91/3.56    inference(cnf_transformation,[],[f44])).
% 24.91/3.56  fof(f44,plain,(
% 24.91/3.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f15])).
% 24.91/3.56  fof(f15,axiom,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 24.91/3.56  fof(f83,plain,(
% 24.91/3.56    ( ! [X0,X1] : (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f56])).
% 24.91/3.56  fof(f56,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(nnf_transformation,[],[f38])).
% 24.91/3.56  fof(f38,plain,(
% 24.91/3.56    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(ennf_transformation,[],[f23])).
% 24.91/3.56  fof(f23,axiom,(
% 24.91/3.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).
% 24.91/3.56  fof(f242,plain,(
% 24.91/3.56    spl4_7),
% 24.91/3.56    inference(avatar_contradiction_clause,[],[f241])).
% 24.91/3.56  fof(f241,plain,(
% 24.91/3.56    $false | spl4_7),
% 24.91/3.56    inference(subsumption_resolution,[],[f239,f72])).
% 24.91/3.56  fof(f239,plain,(
% 24.91/3.56    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl4_7),
% 24.91/3.56    inference(resolution,[],[f211,f91])).
% 24.91/3.56  fof(f91,plain,(
% 24.91/3.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 24.91/3.56    inference(cnf_transformation,[],[f42])).
% 24.91/3.56  fof(f42,plain,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f13])).
% 24.91/3.56  fof(f13,axiom,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 24.91/3.56  fof(f211,plain,(
% 24.91/3.56    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_7),
% 24.91/3.56    inference(avatar_component_clause,[],[f209])).
% 24.91/3.56  fof(f238,plain,(
% 24.91/3.56    ~spl4_7 | spl4_11),
% 24.91/3.56    inference(avatar_split_clause,[],[f233,f235,f209])).
% 24.91/3.56  fof(f233,plain,(
% 24.91/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 24.91/3.56    inference(subsumption_resolution,[],[f232,f71])).
% 24.91/3.56  fof(f232,plain,(
% 24.91/3.56    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 24.91/3.56    inference(superposition,[],[f95,f181])).
% 24.91/3.56  fof(f95,plain,(
% 24.91/3.56    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 24.91/3.56    inference(cnf_transformation,[],[f47])).
% 24.91/3.56  fof(f47,plain,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 24.91/3.56    inference(flattening,[],[f46])).
% 24.91/3.56  fof(f46,plain,(
% 24.91/3.56    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 24.91/3.56    inference(ennf_transformation,[],[f21])).
% 24.91/3.56  fof(f21,axiom,(
% 24.91/3.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 24.91/3.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 24.91/3.56  fof(f155,plain,(
% 24.91/3.56    spl4_1 | spl4_2),
% 24.91/3.56    inference(avatar_split_clause,[],[f73,f151,f147])).
% 24.91/3.56  fof(f73,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 24.91/3.56    inference(cnf_transformation,[],[f55])).
% 24.91/3.56  fof(f154,plain,(
% 24.91/3.56    ~spl4_1 | ~spl4_2),
% 24.91/3.56    inference(avatar_split_clause,[],[f74,f151,f147])).
% 24.91/3.56  fof(f74,plain,(
% 24.91/3.56    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 24.91/3.56    inference(cnf_transformation,[],[f55])).
% 24.91/3.56  % SZS output end Proof for theBenchmark
% 24.91/3.56  % (31994)------------------------------
% 24.91/3.56  % (31994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.91/3.56  % (31994)Termination reason: Refutation
% 24.91/3.56  
% 24.91/3.56  % (31994)Memory used [KB]: 31342
% 24.91/3.56  % (31994)Time elapsed: 2.596 s
% 24.91/3.56  % (31994)------------------------------
% 24.91/3.56  % (31994)------------------------------
% 24.91/3.56  % (31958)Success in time 3.189 s
%------------------------------------------------------------------------------
