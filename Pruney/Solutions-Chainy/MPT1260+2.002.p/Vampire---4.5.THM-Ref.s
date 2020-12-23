%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 6.08s
% Output     : Refutation 6.08s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 582 expanded)
%              Number of leaves         :   29 ( 179 expanded)
%              Depth                    :   17
%              Number of atoms          :  388 (2661 expanded)
%              Number of equality atoms :   91 ( 739 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8514,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f160,f161,f227,f297,f606,f2073,f2149,f2150,f8506])).

fof(f8506,plain,
    ( ~ spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f8505])).

fof(f8505,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_3
    | spl5_4 ),
    inference(subsumption_resolution,[],[f8445,f224])).

fof(f224,plain,
    ( k2_tops_1(sK0,sK1) != k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl5_4
  <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f8445,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f1091,f8422])).

fof(f8422,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f2161,f3156,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3156,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f139,f577])).

fof(f577,plain,(
    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f576,f88])).

fof(f88,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f74,f76,f75])).

fof(f75,plain,
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

fof(f76,plain,
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

fof(f74,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f40])).

fof(f40,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f576,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f574,f89])).

fof(f89,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f77])).

fof(f574,plain,
    ( k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f202,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f202,plain,(
    ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(unit_resulting_resolution,[],[f89,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f130,f109])).

fof(f109,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f139,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f104,f109])).

fof(f104,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f2161,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f88,f149,f89,f89,f154,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

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
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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

fof(f154,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f149,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1091,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f1089,f220])).

fof(f220,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl5_3
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1089,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f177,f145])).

fof(f177,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f88,f89,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f2150,plain,
    ( spl5_2
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f2141,f602,f598,f223,f157])).

fof(f157,plain,
    ( spl5_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f598,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f602,plain,
    ( spl5_8
  <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f2141,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f177,f2139])).

fof(f2139,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f2138,f1886])).

fof(f1886,plain,
    ( ! [X0] : k9_subset_1(k2_pre_topc(sK0,sK1),X0,X0) = X0
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f1678,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ sP4(X0) ) ),
    inference(general_splitting,[],[f129,f150_D])).

fof(f150,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f150_D])).

fof(f150_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f1678,plain,
    ( sP4(k2_pre_topc(sK0,sK1))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f590,f150])).

fof(f590,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_4 ),
    inference(superposition,[],[f105,f225])).

fof(f225,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f223])).

fof(f105,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f2138,plain,
    ( k1_tops_1(sK0,sK1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f2128,f2130])).

fof(f2130,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f2075,f604])).

fof(f604,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f602])).

fof(f2075,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f599,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f599,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f598])).

fof(f2128,plain,
    ( k1_tops_1(sK0,sK1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f2127,f577])).

fof(f2127,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f2077,f2102])).

fof(f2102,plain,
    ( ! [X0] : k6_subset_1(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f599,f145])).

fof(f2077,plain,
    ( k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)))
    | ~ spl5_4
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f590,f599,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f2149,plain,
    ( spl5_1
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f2142,f602,f598,f223,f153])).

fof(f2142,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f178,f2139])).

fof(f178,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f87,f88,f89,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f87,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f2073,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f2072])).

fof(f2072,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f2070,f1444])).

fof(f1444,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f600,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f600,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f598])).

fof(f2070,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[],[f102,f274])).

fof(f274,plain,(
    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f268,f175])).

fof(f175,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f88,f89,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f268,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f89,f179,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f179,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f88,f89,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f102,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f606,plain,
    ( ~ spl5_7
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f592,f223,f602,f598])).

fof(f592,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl5_4 ),
    inference(superposition,[],[f142,f225])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k6_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f113,f109])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f297,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f279,f219])).

fof(f279,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f260,f175])).

fof(f260,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f89,f179,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f227,plain,
    ( ~ spl5_3
    | spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f217,f157,f223,f219])).

fof(f217,plain,
    ( k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f145,f158])).

fof(f158,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f157])).

fof(f161,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f90,f157,f153])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).

fof(f160,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f91,f157,f153])).

fof(f91,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f77])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (1556)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (1577)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.50  % (1564)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (1555)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (1572)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (1554)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (1576)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.55  % (1550)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (1553)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  % (1558)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (1557)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.52/0.55  % (1562)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.52/0.56  % (1561)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.52/0.56  % (1567)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.52/0.56  % (1552)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.52/0.57  % (1578)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.52/0.57  % (1575)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.52/0.57  % (1559)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.52/0.58  % (1574)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.52/0.58  % (1579)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.52/0.58  % (1571)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.52/0.58  % (1566)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.52/0.58  % (1573)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.52/0.58  % (1581)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.52/0.59  % (1570)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.52/0.59  % (1560)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.60  % (1565)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.52/0.60  % (1580)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.52/0.61  % (1568)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.52/0.61  % (1563)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 3.60/0.84  % (1556)Time limit reached!
% 3.60/0.84  % (1556)------------------------------
% 3.60/0.84  % (1556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.60/0.84  % (1556)Termination reason: Time limit
% 3.60/0.84  
% 3.60/0.84  % (1556)Memory used [KB]: 8699
% 3.60/0.84  % (1556)Time elapsed: 0.423 s
% 3.60/0.84  % (1556)------------------------------
% 3.60/0.84  % (1556)------------------------------
% 3.86/0.92  % (1563)Time limit reached!
% 3.86/0.92  % (1563)------------------------------
% 3.86/0.92  % (1563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (1563)Termination reason: Time limit
% 3.86/0.92  % (1563)Termination phase: Saturation
% 3.86/0.92  
% 3.86/0.92  % (1563)Memory used [KB]: 7803
% 3.86/0.92  % (1563)Time elapsed: 0.500 s
% 3.86/0.92  % (1563)------------------------------
% 3.86/0.92  % (1563)------------------------------
% 3.86/0.92  % (1550)Time limit reached!
% 3.86/0.92  % (1550)------------------------------
% 3.86/0.92  % (1550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.86/0.92  % (1550)Termination reason: Time limit
% 3.86/0.92  
% 3.86/0.92  % (1550)Memory used [KB]: 3454
% 3.86/0.92  % (1550)Time elapsed: 0.520 s
% 3.86/0.92  % (1550)------------------------------
% 3.86/0.92  % (1550)------------------------------
% 4.45/0.93  % (1552)Time limit reached!
% 4.45/0.93  % (1552)------------------------------
% 4.45/0.93  % (1552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (1552)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (1552)Memory used [KB]: 7164
% 4.45/0.93  % (1552)Time elapsed: 0.509 s
% 4.45/0.93  % (1552)------------------------------
% 4.45/0.93  % (1552)------------------------------
% 4.45/0.93  % (1568)Time limit reached!
% 4.45/0.93  % (1568)------------------------------
% 4.45/0.93  % (1568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.93  % (1568)Termination reason: Time limit
% 4.45/0.93  
% 4.45/0.93  % (1568)Memory used [KB]: 13048
% 4.45/0.93  % (1568)Time elapsed: 0.507 s
% 4.45/0.93  % (1568)------------------------------
% 4.45/0.93  % (1568)------------------------------
% 4.45/0.94  % (1561)Time limit reached!
% 4.45/0.94  % (1561)------------------------------
% 4.45/0.94  % (1561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.45/0.94  % (1561)Termination reason: Time limit
% 4.45/0.94  
% 4.45/0.94  % (1561)Memory used [KB]: 12792
% 4.45/0.94  % (1561)Time elapsed: 0.526 s
% 4.45/0.94  % (1561)------------------------------
% 4.45/0.94  % (1561)------------------------------
% 4.77/0.98  % (1610)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.77/1.02  % (1558)Time limit reached!
% 4.77/1.02  % (1558)------------------------------
% 4.77/1.02  % (1558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.02  % (1558)Termination reason: Time limit
% 4.77/1.02  
% 4.77/1.02  % (1558)Memory used [KB]: 9722
% 4.77/1.02  % (1558)Time elapsed: 0.608 s
% 4.77/1.02  % (1558)------------------------------
% 4.77/1.02  % (1558)------------------------------
% 4.77/1.03  % (1567)Time limit reached!
% 4.77/1.03  % (1567)------------------------------
% 4.77/1.03  % (1567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.03  % (1567)Termination reason: Time limit
% 4.77/1.03  
% 4.77/1.03  % (1567)Memory used [KB]: 17398
% 4.77/1.03  % (1567)Time elapsed: 0.612 s
% 4.77/1.03  % (1567)------------------------------
% 4.77/1.03  % (1567)------------------------------
% 4.77/1.04  % (1580)Time limit reached!
% 4.77/1.04  % (1580)------------------------------
% 4.77/1.04  % (1580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.77/1.04  % (1580)Termination reason: Time limit
% 4.77/1.04  
% 4.77/1.04  % (1580)Memory used [KB]: 7803
% 4.77/1.04  % (1580)Time elapsed: 0.612 s
% 4.77/1.04  % (1580)------------------------------
% 4.77/1.04  % (1580)------------------------------
% 5.05/1.06  % (1614)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.05/1.06  % (1612)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.05/1.07  % (1613)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.05/1.07  % (1611)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.05/1.07  % (1617)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 6.08/1.15  % (1578)Refutation found. Thanks to Tanya!
% 6.08/1.15  % SZS status Theorem for theBenchmark
% 6.08/1.15  % SZS output start Proof for theBenchmark
% 6.08/1.15  fof(f8514,plain,(
% 6.08/1.15    $false),
% 6.08/1.15    inference(avatar_sat_refutation,[],[f160,f161,f227,f297,f606,f2073,f2149,f2150,f8506])).
% 6.08/1.15  fof(f8506,plain,(
% 6.08/1.15    ~spl5_1 | ~spl5_3 | spl5_4),
% 6.08/1.15    inference(avatar_contradiction_clause,[],[f8505])).
% 6.08/1.15  fof(f8505,plain,(
% 6.08/1.15    $false | (~spl5_1 | ~spl5_3 | spl5_4)),
% 6.08/1.15    inference(subsumption_resolution,[],[f8445,f224])).
% 6.08/1.15  fof(f224,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) != k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | spl5_4),
% 6.08/1.15    inference(avatar_component_clause,[],[f223])).
% 6.08/1.15  fof(f223,plain,(
% 6.08/1.15    spl5_4 <=> k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 6.08/1.15  fof(f8445,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl5_1 | ~spl5_3)),
% 6.08/1.15    inference(backward_demodulation,[],[f1091,f8422])).
% 6.08/1.15  fof(f8422,plain,(
% 6.08/1.15    sK1 = k1_tops_1(sK0,sK1) | ~spl5_1),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f2161,f3156,f122])).
% 6.08/1.15  fof(f122,plain,(
% 6.08/1.15    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f81])).
% 6.08/1.15  fof(f81,plain,(
% 6.08/1.15    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.08/1.15    inference(flattening,[],[f80])).
% 6.08/1.15  fof(f80,plain,(
% 6.08/1.15    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.08/1.15    inference(nnf_transformation,[],[f4])).
% 6.08/1.15  fof(f4,axiom,(
% 6.08/1.15    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.08/1.15  fof(f3156,plain,(
% 6.08/1.15    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 6.08/1.15    inference(superposition,[],[f139,f577])).
% 6.08/1.15  fof(f577,plain,(
% 6.08/1.15    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 6.08/1.15    inference(subsumption_resolution,[],[f576,f88])).
% 6.08/1.15  fof(f88,plain,(
% 6.08/1.15    l1_pre_topc(sK0)),
% 6.08/1.15    inference(cnf_transformation,[],[f77])).
% 6.08/1.15  fof(f77,plain,(
% 6.08/1.15    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.08/1.15    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f74,f76,f75])).
% 6.08/1.15  fof(f75,plain,(
% 6.08/1.15    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.08/1.15    introduced(choice_axiom,[])).
% 6.08/1.15  fof(f76,plain,(
% 6.08/1.15    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.08/1.15    introduced(choice_axiom,[])).
% 6.08/1.15  fof(f74,plain,(
% 6.08/1.15    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.08/1.15    inference(flattening,[],[f73])).
% 6.08/1.15  fof(f73,plain,(
% 6.08/1.15    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.08/1.15    inference(nnf_transformation,[],[f44])).
% 6.08/1.15  fof(f44,plain,(
% 6.08/1.15    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.08/1.15    inference(flattening,[],[f43])).
% 6.08/1.15  fof(f43,plain,(
% 6.08/1.15    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f41])).
% 6.08/1.15  fof(f41,negated_conjecture,(
% 6.08/1.15    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 6.08/1.15    inference(negated_conjecture,[],[f40])).
% 6.08/1.15  fof(f40,conjecture,(
% 6.08/1.15    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 6.08/1.15  fof(f576,plain,(
% 6.08/1.15    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 6.08/1.15    inference(subsumption_resolution,[],[f574,f89])).
% 6.08/1.15  fof(f89,plain,(
% 6.08/1.15    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    inference(cnf_transformation,[],[f77])).
% 6.08/1.15  fof(f574,plain,(
% 6.08/1.15    k1_tops_1(sK0,sK1) = k6_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 6.08/1.15    inference(superposition,[],[f202,f96])).
% 6.08/1.15  fof(f96,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f47])).
% 6.08/1.15  fof(f47,plain,(
% 6.08/1.15    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(ennf_transformation,[],[f39])).
% 6.08/1.15  fof(f39,axiom,(
% 6.08/1.15    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 6.08/1.15  fof(f202,plain,(
% 6.08/1.15    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0)) )),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f89,f145])).
% 6.08/1.15  fof(f145,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(definition_unfolding,[],[f130,f109])).
% 6.08/1.15  fof(f109,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f28])).
% 6.08/1.15  fof(f28,axiom,(
% 6.08/1.15    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 6.08/1.15  fof(f130,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f64])).
% 6.08/1.15  fof(f64,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f29])).
% 6.08/1.15  fof(f29,axiom,(
% 6.08/1.15    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.08/1.15  fof(f139,plain,(
% 6.08/1.15    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 6.08/1.15    inference(definition_unfolding,[],[f104,f109])).
% 6.08/1.15  fof(f104,plain,(
% 6.08/1.15    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f9])).
% 6.08/1.15  fof(f9,axiom,(
% 6.08/1.15    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.08/1.15  fof(f2161,plain,(
% 6.08/1.15    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl5_1),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f88,f149,f89,f89,f154,f98])).
% 6.08/1.15  fof(f98,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f50])).
% 6.08/1.15  fof(f50,plain,(
% 6.08/1.15    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(flattening,[],[f49])).
% 6.08/1.15  fof(f49,plain,(
% 6.08/1.15    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(ennf_transformation,[],[f36])).
% 6.08/1.15  fof(f36,axiom,(
% 6.08/1.15    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 6.08/1.15  fof(f154,plain,(
% 6.08/1.15    v3_pre_topc(sK1,sK0) | ~spl5_1),
% 6.08/1.15    inference(avatar_component_clause,[],[f153])).
% 6.08/1.15  fof(f153,plain,(
% 6.08/1.15    spl5_1 <=> v3_pre_topc(sK1,sK0)),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 6.08/1.15  fof(f149,plain,(
% 6.08/1.15    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.08/1.15    inference(equality_resolution,[],[f120])).
% 6.08/1.15  fof(f120,plain,(
% 6.08/1.15    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 6.08/1.15    inference(cnf_transformation,[],[f81])).
% 6.08/1.15  fof(f1091,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl5_3),
% 6.08/1.15    inference(subsumption_resolution,[],[f1089,f220])).
% 6.08/1.15  fof(f220,plain,(
% 6.08/1.15    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 6.08/1.15    inference(avatar_component_clause,[],[f219])).
% 6.08/1.15  fof(f219,plain,(
% 6.08/1.15    spl5_3 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 6.08/1.15  fof(f1089,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    inference(superposition,[],[f177,f145])).
% 6.08/1.15  fof(f177,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f88,f89,f97])).
% 6.08/1.15  fof(f97,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f48])).
% 6.08/1.15  fof(f48,plain,(
% 6.08/1.15    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(ennf_transformation,[],[f35])).
% 6.08/1.15  fof(f35,axiom,(
% 6.08/1.15    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 6.08/1.15  fof(f2150,plain,(
% 6.08/1.15    spl5_2 | ~spl5_4 | ~spl5_7 | ~spl5_8),
% 6.08/1.15    inference(avatar_split_clause,[],[f2141,f602,f598,f223,f157])).
% 6.08/1.15  fof(f157,plain,(
% 6.08/1.15    spl5_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 6.08/1.15  fof(f598,plain,(
% 6.08/1.15    spl5_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 6.08/1.15  fof(f602,plain,(
% 6.08/1.15    spl5_8 <=> k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)),
% 6.08/1.15    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 6.08/1.15  fof(f2141,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl5_4 | ~spl5_7 | ~spl5_8)),
% 6.08/1.15    inference(backward_demodulation,[],[f177,f2139])).
% 6.08/1.15  fof(f2139,plain,(
% 6.08/1.15    sK1 = k1_tops_1(sK0,sK1) | (~spl5_4 | ~spl5_7 | ~spl5_8)),
% 6.08/1.15    inference(forward_demodulation,[],[f2138,f1886])).
% 6.08/1.15  fof(f1886,plain,(
% 6.08/1.15    ( ! [X0] : (k9_subset_1(k2_pre_topc(sK0,sK1),X0,X0) = X0) ) | ~spl5_4),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f1678,f151])).
% 6.08/1.15  fof(f151,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~sP4(X0)) )),
% 6.08/1.15    inference(general_splitting,[],[f129,f150_D])).
% 6.08/1.15  fof(f150,plain,(
% 6.08/1.15    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | sP4(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f150_D])).
% 6.08/1.15  fof(f150_D,plain,(
% 6.08/1.15    ( ! [X0] : (( ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(X0)) ) <=> ~sP4(X0)) )),
% 6.08/1.15    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 6.08/1.15  fof(f129,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f63])).
% 6.08/1.15  fof(f63,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f24])).
% 6.08/1.15  fof(f24,axiom,(
% 6.08/1.15    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 6.08/1.15  fof(f1678,plain,(
% 6.08/1.15    sP4(k2_pre_topc(sK0,sK1)) | ~spl5_4),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f590,f150])).
% 6.08/1.15  fof(f590,plain,(
% 6.08/1.15    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl5_4),
% 6.08/1.15    inference(superposition,[],[f105,f225])).
% 6.08/1.15  fof(f225,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl5_4),
% 6.08/1.15    inference(avatar_component_clause,[],[f223])).
% 6.08/1.15  fof(f105,plain,(
% 6.08/1.15    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f22])).
% 6.08/1.15  fof(f22,axiom,(
% 6.08/1.15    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 6.08/1.15  fof(f2138,plain,(
% 6.08/1.15    k1_tops_1(sK0,sK1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,sK1) | (~spl5_4 | ~spl5_7 | ~spl5_8)),
% 6.08/1.15    inference(backward_demodulation,[],[f2128,f2130])).
% 6.08/1.15  fof(f2130,plain,(
% 6.08/1.15    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl5_7 | ~spl5_8)),
% 6.08/1.15    inference(forward_demodulation,[],[f2075,f604])).
% 6.08/1.15  fof(f604,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl5_8),
% 6.08/1.15    inference(avatar_component_clause,[],[f602])).
% 6.08/1.15  fof(f2075,plain,(
% 6.08/1.15    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl5_7),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f599,f114])).
% 6.08/1.15  fof(f114,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f54])).
% 6.08/1.15  fof(f54,plain,(
% 6.08/1.15    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f25])).
% 6.08/1.15  fof(f25,axiom,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 6.08/1.15  fof(f599,plain,(
% 6.08/1.15    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl5_7),
% 6.08/1.15    inference(avatar_component_clause,[],[f598])).
% 6.08/1.15  fof(f2128,plain,(
% 6.08/1.15    k1_tops_1(sK0,sK1) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl5_4 | ~spl5_7)),
% 6.08/1.15    inference(forward_demodulation,[],[f2127,f577])).
% 6.08/1.15  fof(f2127,plain,(
% 6.08/1.15    k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl5_4 | ~spl5_7)),
% 6.08/1.15    inference(forward_demodulation,[],[f2077,f2102])).
% 6.08/1.15  fof(f2102,plain,(
% 6.08/1.15    ( ! [X0] : (k6_subset_1(sK1,X0) = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,X0)) ) | ~spl5_7),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f599,f145])).
% 6.08/1.15  fof(f2077,plain,(
% 6.08/1.15    k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) = k9_subset_1(k2_pre_topc(sK0,sK1),sK1,k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))) | (~spl5_4 | ~spl5_7)),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f590,f599,f116])).
% 6.08/1.15  fof(f116,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f56])).
% 6.08/1.15  fof(f56,plain,(
% 6.08/1.15    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f30])).
% 6.08/1.15  fof(f30,axiom,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 6.08/1.15  fof(f2149,plain,(
% 6.08/1.15    spl5_1 | ~spl5_4 | ~spl5_7 | ~spl5_8),
% 6.08/1.15    inference(avatar_split_clause,[],[f2142,f602,f598,f223,f153])).
% 6.08/1.15  fof(f2142,plain,(
% 6.08/1.15    v3_pre_topc(sK1,sK0) | (~spl5_4 | ~spl5_7 | ~spl5_8)),
% 6.08/1.15    inference(backward_demodulation,[],[f178,f2139])).
% 6.08/1.15  fof(f178,plain,(
% 6.08/1.15    v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f87,f88,f89,f118])).
% 6.08/1.15  fof(f118,plain,(
% 6.08/1.15    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f59])).
% 6.08/1.15  fof(f59,plain,(
% 6.08/1.15    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.08/1.15    inference(flattening,[],[f58])).
% 6.08/1.15  fof(f58,plain,(
% 6.08/1.15    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f34])).
% 6.08/1.15  fof(f34,axiom,(
% 6.08/1.15    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 6.08/1.15  fof(f87,plain,(
% 6.08/1.15    v2_pre_topc(sK0)),
% 6.08/1.15    inference(cnf_transformation,[],[f77])).
% 6.08/1.15  fof(f2073,plain,(
% 6.08/1.15    spl5_7),
% 6.08/1.15    inference(avatar_contradiction_clause,[],[f2072])).
% 6.08/1.15  fof(f2072,plain,(
% 6.08/1.15    $false | spl5_7),
% 6.08/1.15    inference(subsumption_resolution,[],[f2070,f1444])).
% 6.08/1.15  fof(f1444,plain,(
% 6.08/1.15    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl5_7),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f600,f127])).
% 6.08/1.15  fof(f127,plain,(
% 6.08/1.15    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f86])).
% 6.08/1.15  fof(f86,plain,(
% 6.08/1.15    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.08/1.15    inference(nnf_transformation,[],[f32])).
% 6.08/1.15  fof(f32,axiom,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.08/1.15  fof(f600,plain,(
% 6.08/1.15    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl5_7),
% 6.08/1.15    inference(avatar_component_clause,[],[f598])).
% 6.08/1.15  fof(f2070,plain,(
% 6.08/1.15    r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 6.08/1.15    inference(superposition,[],[f102,f274])).
% 6.08/1.15  fof(f274,plain,(
% 6.08/1.15    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 6.08/1.15    inference(forward_demodulation,[],[f268,f175])).
% 6.08/1.15  fof(f175,plain,(
% 6.08/1.15    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f88,f89,f95])).
% 6.08/1.15  fof(f95,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f46])).
% 6.08/1.15  fof(f46,plain,(
% 6.08/1.15    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(ennf_transformation,[],[f38])).
% 6.08/1.15  fof(f38,axiom,(
% 6.08/1.15    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 6.08/1.15  fof(f268,plain,(
% 6.08/1.15    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f89,f179,f135])).
% 6.08/1.15  fof(f135,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f72])).
% 6.08/1.15  fof(f72,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(flattening,[],[f71])).
% 6.08/1.15  fof(f71,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.08/1.15    inference(ennf_transformation,[],[f27])).
% 6.08/1.15  fof(f27,axiom,(
% 6.08/1.15    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 6.08/1.15  fof(f179,plain,(
% 6.08/1.15    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f88,f89,f119])).
% 6.08/1.15  fof(f119,plain,(
% 6.08/1.15    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.08/1.15    inference(cnf_transformation,[],[f61])).
% 6.08/1.15  fof(f61,plain,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.08/1.15    inference(flattening,[],[f60])).
% 6.08/1.15  fof(f60,plain,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f33])).
% 6.08/1.15  fof(f33,axiom,(
% 6.08/1.15    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 6.08/1.15  fof(f102,plain,(
% 6.08/1.15    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f17])).
% 6.08/1.15  fof(f17,axiom,(
% 6.08/1.15    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.08/1.15  fof(f606,plain,(
% 6.08/1.15    ~spl5_7 | spl5_8 | ~spl5_4),
% 6.08/1.15    inference(avatar_split_clause,[],[f592,f223,f602,f598])).
% 6.08/1.15  fof(f592,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl5_4),
% 6.08/1.15    inference(superposition,[],[f142,f225])).
% 6.08/1.15  fof(f142,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k6_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(definition_unfolding,[],[f113,f109])).
% 6.08/1.15  fof(f113,plain,(
% 6.08/1.15    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f53])).
% 6.08/1.15  fof(f53,plain,(
% 6.08/1.15    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(ennf_transformation,[],[f19])).
% 6.08/1.15  fof(f19,axiom,(
% 6.08/1.15    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 6.08/1.15  fof(f297,plain,(
% 6.08/1.15    spl5_3),
% 6.08/1.15    inference(avatar_split_clause,[],[f279,f219])).
% 6.08/1.15  fof(f279,plain,(
% 6.08/1.15    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    inference(forward_demodulation,[],[f260,f175])).
% 6.08/1.15  fof(f260,plain,(
% 6.08/1.15    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.08/1.15    inference(unit_resulting_resolution,[],[f89,f179,f134])).
% 6.08/1.15  fof(f134,plain,(
% 6.08/1.15    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.08/1.15    inference(cnf_transformation,[],[f70])).
% 6.08/1.15  fof(f70,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.08/1.15    inference(flattening,[],[f69])).
% 6.08/1.15  fof(f69,plain,(
% 6.08/1.15    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.08/1.15    inference(ennf_transformation,[],[f21])).
% 6.08/1.15  fof(f21,axiom,(
% 6.08/1.15    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 6.08/1.15    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 6.08/1.15  fof(f227,plain,(
% 6.08/1.15    ~spl5_3 | spl5_4 | ~spl5_2),
% 6.08/1.15    inference(avatar_split_clause,[],[f217,f157,f223,f219])).
% 6.08/1.15  fof(f217,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k6_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_2),
% 6.08/1.15    inference(superposition,[],[f145,f158])).
% 6.08/1.15  fof(f158,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl5_2),
% 6.08/1.15    inference(avatar_component_clause,[],[f157])).
% 6.08/1.15  fof(f161,plain,(
% 6.08/1.15    spl5_1 | spl5_2),
% 6.08/1.15    inference(avatar_split_clause,[],[f90,f157,f153])).
% 6.08/1.15  fof(f90,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 6.08/1.15    inference(cnf_transformation,[],[f77])).
% 6.08/1.15  fof(f160,plain,(
% 6.08/1.15    ~spl5_1 | ~spl5_2),
% 6.08/1.15    inference(avatar_split_clause,[],[f91,f157,f153])).
% 6.08/1.15  fof(f91,plain,(
% 6.08/1.15    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 6.08/1.15    inference(cnf_transformation,[],[f77])).
% 6.08/1.15  % SZS output end Proof for theBenchmark
% 6.08/1.15  % (1578)------------------------------
% 6.08/1.15  % (1578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.08/1.15  % (1578)Termination reason: Refutation
% 6.08/1.15  
% 6.08/1.15  % (1578)Memory used [KB]: 15607
% 6.08/1.15  % (1578)Time elapsed: 0.722 s
% 6.08/1.15  % (1578)------------------------------
% 6.08/1.15  % (1578)------------------------------
% 6.08/1.15  % (1549)Success in time 0.786 s
%------------------------------------------------------------------------------
