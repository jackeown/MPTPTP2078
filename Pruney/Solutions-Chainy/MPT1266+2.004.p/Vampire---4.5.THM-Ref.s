%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 804 expanded)
%              Number of leaves         :   24 ( 240 expanded)
%              Depth                    :   26
%              Number of atoms          :  356 (2860 expanded)
%              Number of equality atoms :   79 ( 912 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f107,f238,f403,f408,f416,f439])).

fof(f439,plain,
    ( ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl2_1
    | spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f437,f105])).

fof(f105,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl2_2
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f437,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f436,f124])).

fof(f124,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(subsumption_resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f122,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_subset_1(X0,X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f84,f95])).

fof(f95,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f66,f93])).

fof(f93,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f70,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f70,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f436,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f315,f422])).

fof(f422,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f421,f335])).

fof(f335,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f334,f95])).

fof(f334,plain,(
    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f331,f168])).

fof(f168,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f167,f60])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,
    ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
      | ~ v2_tops_1(sK1,sK0) )
    & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k1_xboole_0 != k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
            | ~ v2_tops_1(X1,sK0) )
          & ( k1_xboole_0 = k1_tops_1(sK0,X1)
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X1] :
        ( ( k1_xboole_0 != k1_tops_1(sK0,X1)
          | ~ v2_tops_1(X1,sK0) )
        & ( k1_xboole_0 = k1_tops_1(sK0,X1)
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k1_xboole_0 != k1_tops_1(sK0,sK1)
        | ~ v2_tops_1(sK1,sK0) )
      & ( k1_xboole_0 = k1_tops_1(sK0,sK1)
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k1_xboole_0 != k1_tops_1(X0,X1)
            | ~ v2_tops_1(X1,X0) )
          & ( k1_xboole_0 = k1_tops_1(X0,X1)
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> k1_xboole_0 = k1_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f167,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f165,f109])).

fof(f109,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f69,f93])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f165,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f86,f163])).

fof(f163,plain,(
    k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f162,f60])).

fof(f162,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f161,f109])).

fof(f161,plain,
    ( k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f160,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f160,plain,(
    v1_tops_1(u1_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f159,f95])).

fof(f159,plain,(
    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f157,f67])).

fof(f157,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f156,f64])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f156,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f154,f125])).

fof(f125,plain,(
    ! [X0] :
      ( v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f74,f60])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).

fof(f154,plain,(
    ! [X0] :
      ( ~ v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f331,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f84,f319])).

fof(f319,plain,(
    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f318,f116])).

fof(f116,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f112,f115])).

fof(f115,plain,(
    k1_xboole_0 = k1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f114,f112])).

fof(f114,plain,(
    k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(resolution,[],[f72,f60])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).

fof(f112,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(resolution,[],[f110,f60])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(resolution,[],[f71,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f71,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).

fof(f318,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f317,f163])).

fof(f317,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f308,f95])).

fof(f308,plain,(
    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))) ),
    inference(resolution,[],[f305,f67])).

fof(f305,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    inference(resolution,[],[f73,f60])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).

fof(f421,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f420,f60])).

fof(f420,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f419,f228])).

fof(f228,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl2_5
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f419,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f418,f75])).

fof(f418,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f417,f61])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f417,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f100,f154])).

fof(f100,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_1
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f315,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f305,f61])).

fof(f416,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f414,f60])).

fof(f414,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_5
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f413,f228])).

fof(f413,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_1
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f412,f180])).

fof(f180,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_1 ),
    inference(subsumption_resolution,[],[f177,f61])).

fof(f177,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl2_1 ),
    inference(resolution,[],[f176,f101])).

fof(f101,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f176,plain,(
    ! [X0] :
      ( v2_tops_1(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) ) ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f412,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f410,f335])).

fof(f410,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_23 ),
    inference(superposition,[],[f76,f402])).

fof(f402,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl2_23
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f408,plain,
    ( ~ spl2_5
    | spl2_22 ),
    inference(avatar_contradiction_clause,[],[f407])).

fof(f407,plain,
    ( $false
    | ~ spl2_5
    | spl2_22 ),
    inference(subsumption_resolution,[],[f406,f60])).

fof(f406,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_5
    | spl2_22 ),
    inference(subsumption_resolution,[],[f404,f228])).

fof(f404,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_22 ),
    inference(resolution,[],[f398,f86])).

fof(f398,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl2_22
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f403,plain,
    ( ~ spl2_22
    | spl2_23
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f394,f103,f400,f396])).

fof(f394,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f392,f95])).

fof(f392,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f84,f323])).

fof(f323,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f315,f104])).

fof(f104,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f238,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl2_5 ),
    inference(subsumption_resolution,[],[f235,f61])).

fof(f235,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(resolution,[],[f229,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f229,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f227])).

fof(f107,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f62,f103,f99])).

fof(f62,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

fof(f106,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f63,f103,f99])).

fof(f63,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:15:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (7857)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (7849)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (7865)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (7865)Refutation not found, incomplete strategy% (7865)------------------------------
% 0.22/0.54  % (7865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7848)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (7865)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7865)Memory used [KB]: 10746
% 0.22/0.54  % (7865)Time elapsed: 0.122 s
% 0.22/0.54  % (7865)------------------------------
% 0.22/0.54  % (7865)------------------------------
% 0.22/0.54  % (7847)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (7843)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.55  % (7870)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (7845)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (7844)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.55  % (7858)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (7853)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (7846)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.55  % (7852)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (7872)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (7871)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (7867)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (7863)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (7856)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (7866)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  % (7862)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (7869)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (7859)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (7860)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (7864)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (7855)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (7854)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (7850)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (7861)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (7851)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (7845)Refutation not found, incomplete strategy% (7845)------------------------------
% 0.22/0.57  % (7845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (7845)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (7845)Memory used [KB]: 10746
% 0.22/0.57  % (7845)Time elapsed: 0.155 s
% 0.22/0.57  % (7845)------------------------------
% 0.22/0.57  % (7845)------------------------------
% 0.22/0.58  % (7846)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f440,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f106,f107,f238,f403,f408,f416,f439])).
% 0.22/0.58  fof(f439,plain,(
% 0.22/0.58    ~spl2_1 | spl2_2 | ~spl2_5),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f438])).
% 0.22/0.58  fof(f438,plain,(
% 0.22/0.58    $false | (~spl2_1 | spl2_2 | ~spl2_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f437,f105])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl2_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f103])).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    spl2_2 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.58  fof(f437,plain,(
% 0.22/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_5)),
% 0.22/0.58    inference(forward_demodulation,[],[f436,f124])).
% 0.22/0.58  fof(f124,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 0.22/0.58    inference(subsumption_resolution,[],[f122,f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,axiom,(
% 0.22/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.58  fof(f122,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(superposition,[],[f84,f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.58    inference(definition_unfolding,[],[f66,f93])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f70,f65])).
% 0.22/0.58  fof(f65,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.58  fof(f84,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.58  fof(f436,plain,(
% 0.22/0.58    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl2_1 | ~spl2_5)),
% 0.22/0.58    inference(forward_demodulation,[],[f315,f422])).
% 0.22/0.58  fof(f422,plain,(
% 0.22/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_5)),
% 0.22/0.58    inference(forward_demodulation,[],[f421,f335])).
% 0.22/0.58  fof(f335,plain,(
% 0.22/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f334,f95])).
% 0.22/0.58  fof(f334,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f331,f168])).
% 0.22/0.58  fof(f168,plain,(
% 0.22/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(subsumption_resolution,[],[f167,f60])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    l1_pre_topc(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f53,f55,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    ? [X1] : ((k1_xboole_0 != k1_tops_1(sK0,X1) | ~v2_tops_1(X1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,X1) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)) & (k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f53,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (((k1_xboole_0 != k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) & (k1_xboole_0 = k1_tops_1(X0,X1) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f29])).
% 0.22/0.58  fof(f29,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> k1_xboole_0 = k1_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f28])).
% 0.22/0.58  fof(f28,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.58    inference(negated_conjecture,[],[f27])).
% 0.22/0.58  fof(f27,conjecture,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.58  fof(f167,plain,(
% 0.22/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f165,f109])).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(forward_demodulation,[],[f96,f95])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(definition_unfolding,[],[f69,f93])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f10])).
% 0.22/0.58  fof(f10,axiom,(
% 0.22/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(superposition,[],[f86,f163])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f162,f60])).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f161,f109])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    k2_pre_topc(sK0,u1_struct_0(sK0)) = k2_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.58    inference(resolution,[],[f160,f75])).
% 0.22/0.58  fof(f75,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f35])).
% 0.22/0.58  fof(f35,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f21])).
% 0.22/0.58  fof(f21,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    v1_tops_1(u1_struct_0(sK0),sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f159,f95])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f157,f67])).
% 0.22/0.58  fof(f157,plain,(
% 0.22/0.58    v1_tops_1(k3_subset_1(u1_struct_0(sK0),k1_xboole_0),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(resolution,[],[f156,f64])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    inference(cnf_transformation,[],[f1])).
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    v1_xboole_0(k1_xboole_0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.58  fof(f156,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(X0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f155])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.58    inference(resolution,[],[f154,f125])).
% 0.22/0.58  fof(f125,plain,(
% 0.22/0.58    ( ! [X0] : (v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0)) )),
% 0.22/0.58    inference(resolution,[],[f74,f60])).
% 0.22/0.58  fof(f74,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f34,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f33])).
% 0.22/0.58  fof(f33,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f19])).
% 0.22/0.58  fof(f19,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v2_tops_1(X1,X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tops_1)).
% 0.22/0.58  fof(f154,plain,(
% 0.22/0.58    ( ! [X0] : (~v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.58    inference(resolution,[],[f77,f60])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(nnf_transformation,[],[f36])).
% 0.22/0.58  fof(f36,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(flattening,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f18])).
% 0.22/0.58  fof(f18,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.58  fof(f331,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(superposition,[],[f84,f319])).
% 0.22/0.58  fof(f319,plain,(
% 0.22/0.58    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.58    inference(forward_demodulation,[],[f318,f116])).
% 0.22/0.58  fof(f116,plain,(
% 0.22/0.58    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.22/0.58    inference(backward_demodulation,[],[f112,f115])).
% 0.22/0.58  fof(f115,plain,(
% 0.22/0.58    k1_xboole_0 = k1_struct_0(sK0)),
% 0.22/0.58    inference(forward_demodulation,[],[f114,f112])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    k1_struct_0(sK0) = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.58    inference(resolution,[],[f72,f60])).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(X0) | k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f31])).
% 0.22/0.58  fof(f31,plain,(
% 0.22/0.58    ! [X0] : (k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f26])).
% 0.22/0.58  fof(f26,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_tops_1)).
% 0.22/0.58  fof(f112,plain,(
% 0.22/0.58    k1_xboole_0 = k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.22/0.58    inference(resolution,[],[f110,f60])).
% 0.22/0.58  fof(f110,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,k1_struct_0(X0))) )),
% 0.22/0.58    inference(resolution,[],[f71,f79])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.58  fof(f71,plain,(
% 0.22/0.58    ( ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f30])).
% 0.22/0.58  fof(f30,plain,(
% 0.22/0.58    ! [X0] : (v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => v1_xboole_0(k1_tops_1(X0,k1_struct_0(X0))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_tops_1)).
% 0.22/0.58  fof(f318,plain,(
% 0.22/0.58    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 0.22/0.58    inference(forward_demodulation,[],[f317,f163])).
% 0.22/0.58  fof(f317,plain,(
% 0.22/0.58    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,u1_struct_0(sK0)))),
% 0.22/0.58    inference(forward_demodulation,[],[f308,f95])).
% 0.22/0.58  fof(f308,plain,(
% 0.22/0.58    k1_tops_1(sK0,k1_xboole_0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0)))),
% 0.22/0.58    inference(resolution,[],[f305,f67])).
% 0.22/0.58  fof(f305,plain,(
% 0.22/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) )),
% 0.22/0.58    inference(resolution,[],[f73,f60])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f32])).
% 0.22/0.58  fof(f32,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,axiom,(
% 0.22/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.58  fof(f421,plain,(
% 0.22/0.58    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_1 | ~spl2_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f420,f60])).
% 0.22/0.58  fof(f420,plain,(
% 0.22/0.58    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0) | (~spl2_1 | ~spl2_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f419,f228])).
% 0.22/0.58  fof(f228,plain,(
% 0.22/0.58    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f227])).
% 0.22/0.58  fof(f227,plain,(
% 0.22/0.58    spl2_5 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.58  fof(f419,plain,(
% 0.22/0.58    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_1),
% 0.22/0.58    inference(resolution,[],[f418,f75])).
% 0.22/0.58  fof(f418,plain,(
% 0.22/0.58    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_1),
% 0.22/0.58    inference(subsumption_resolution,[],[f417,f61])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    inference(cnf_transformation,[],[f56])).
% 0.22/0.58  fof(f417,plain,(
% 0.22/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_1),
% 0.22/0.58    inference(resolution,[],[f100,f154])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    v2_tops_1(sK1,sK0) | ~spl2_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f99])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    spl2_1 <=> v2_tops_1(sK1,sK0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.58  fof(f315,plain,(
% 0.22/0.58    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.58    inference(resolution,[],[f305,f61])).
% 0.22/0.58  fof(f416,plain,(
% 0.22/0.58    spl2_1 | ~spl2_5 | ~spl2_23),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f415])).
% 0.22/0.58  fof(f415,plain,(
% 0.22/0.58    $false | (spl2_1 | ~spl2_5 | ~spl2_23)),
% 0.22/0.58    inference(subsumption_resolution,[],[f414,f60])).
% 0.22/0.58  fof(f414,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_5 | ~spl2_23)),
% 0.22/0.58    inference(subsumption_resolution,[],[f413,f228])).
% 0.22/0.58  fof(f413,plain,(
% 0.22/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_1 | ~spl2_23)),
% 0.22/0.58    inference(subsumption_resolution,[],[f412,f180])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_1),
% 0.22/0.58    inference(subsumption_resolution,[],[f177,f61])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | spl2_1),
% 0.22/0.58    inference(resolution,[],[f176,f101])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    ~v2_tops_1(sK1,sK0) | spl2_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f99])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    ( ! [X0] : (v2_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(k3_subset_1(u1_struct_0(sK0),X0),sK0)) )),
% 0.22/0.58    inference(resolution,[],[f78,f60])).
% 0.22/0.58  fof(f78,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f58])).
% 0.22/0.58  fof(f412,plain,(
% 0.22/0.58    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_23),
% 0.22/0.58    inference(subsumption_resolution,[],[f410,f335])).
% 0.22/0.58  fof(f410,plain,(
% 0.22/0.58    u1_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_23),
% 0.22/0.58    inference(superposition,[],[f76,f402])).
% 0.22/0.58  fof(f402,plain,(
% 0.22/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_23),
% 0.22/0.58    inference(avatar_component_clause,[],[f400])).
% 0.22/0.58  fof(f400,plain,(
% 0.22/0.58    spl2_23 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.58  fof(f76,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f57])).
% 0.22/0.58  fof(f408,plain,(
% 0.22/0.58    ~spl2_5 | spl2_22),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f407])).
% 0.22/0.58  fof(f407,plain,(
% 0.22/0.58    $false | (~spl2_5 | spl2_22)),
% 0.22/0.58    inference(subsumption_resolution,[],[f406,f60])).
% 0.22/0.58  fof(f406,plain,(
% 0.22/0.58    ~l1_pre_topc(sK0) | (~spl2_5 | spl2_22)),
% 0.22/0.58    inference(subsumption_resolution,[],[f404,f228])).
% 0.22/0.58  fof(f404,plain,(
% 0.22/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_22),
% 0.22/0.58    inference(resolution,[],[f398,f86])).
% 0.22/0.58  fof(f398,plain,(
% 0.22/0.58    ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_22),
% 0.22/0.58    inference(avatar_component_clause,[],[f396])).
% 0.22/0.58  fof(f396,plain,(
% 0.22/0.58    spl2_22 <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.58  fof(f403,plain,(
% 0.22/0.58    ~spl2_22 | spl2_23 | ~spl2_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f394,f103,f400,f396])).
% 0.22/0.58  fof(f394,plain,(
% 0.22/0.58    u1_struct_0(sK0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.58    inference(forward_demodulation,[],[f392,f95])).
% 0.22/0.58  fof(f392,plain,(
% 0.22/0.58    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.58    inference(superposition,[],[f84,f323])).
% 0.22/0.58  fof(f323,plain,(
% 0.22/0.58    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_2),
% 0.22/0.58    inference(forward_demodulation,[],[f315,f104])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f103])).
% 0.22/0.58  fof(f238,plain,(
% 0.22/0.58    spl2_5),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f237])).
% 0.22/0.58  fof(f237,plain,(
% 0.22/0.58    $false | spl2_5),
% 0.22/0.58    inference(subsumption_resolution,[],[f235,f61])).
% 0.22/0.58  fof(f235,plain,(
% 0.22/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 0.22/0.58    inference(resolution,[],[f229,f83])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.58  fof(f229,plain,(
% 0.22/0.58    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f227])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    spl2_1 | spl2_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f62,f103,f99])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f56])).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    ~spl2_1 | ~spl2_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f63,f103,f99])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    k1_xboole_0 != k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f56])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (7846)------------------------------
% 0.22/0.58  % (7846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (7846)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (7846)Memory used [KB]: 11001
% 0.22/0.58  % (7846)Time elapsed: 0.164 s
% 0.22/0.58  % (7846)------------------------------
% 0.22/0.58  % (7846)------------------------------
% 0.22/0.58  % (7868)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (7842)Success in time 0.212 s
%------------------------------------------------------------------------------
