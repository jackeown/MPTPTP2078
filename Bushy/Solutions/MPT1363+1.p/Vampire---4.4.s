%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : compts_1__t18_compts_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:50 EDT 2019

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  125 (1122 expanded)
%              Number of leaves         :   21 ( 406 expanded)
%              Depth                    :   19
%              Number of atoms          :  535 (8358 expanded)
%              Number of equality atoms :   55 ( 222 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f793,f831,f1481,f1643,f2061,f2081,f2379])).

fof(f2379,plain,(
    ~ spl9_124 ),
    inference(avatar_contradiction_clause,[],[f2378])).

fof(f2378,plain,
    ( $false
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f2377,f95])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ~ v2_compts_1(sK2,sK0)
    & v4_pre_topc(sK2,sK0)
    & r1_tarski(sK2,sK1)
    & v2_compts_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f75,f74,f73])).

fof(f73,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_compts_1(X2,X0)
                & v4_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & v2_compts_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,sK0)
              & v4_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & v4_pre_topc(X2,X0)
            & r1_tarski(X2,sK1)
            & v2_compts_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & v4_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & v2_compts_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK2,X0)
        & v4_pre_topc(sK2,X0)
        & r1_tarski(sK2,X1)
        & v2_compts_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_compts_1(X2,X0)
              & v4_pre_topc(X2,X0)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & r1_tarski(X2,X1)
                    & v2_compts_1(X1,X0) )
                 => v2_compts_1(X2,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & v2_compts_1(X1,X0) )
               => v2_compts_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',t18_compts_1)).

fof(f2377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f2376,f99])).

fof(f99,plain,(
    ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f2376,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_124 ),
    inference(subsumption_resolution,[],[f2375,f93])).

fof(f93,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f2375,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_compts_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_124 ),
    inference(resolution,[],[f786,f220])).

fof(f220,plain,(
    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f195,f93])).

fof(f195,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',dt_k1_pre_topc)).

fof(f94,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f76])).

fof(f786,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_compts_1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f785])).

fof(f785,plain,
    ( spl9_124
  <=> ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f2081,plain,
    ( spl9_10
    | spl9_12 ),
    inference(avatar_split_clause,[],[f2080,f216,f210])).

fof(f210,plain,
    ( spl9_10
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f216,plain,
    ( spl9_12
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f2080,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2079,f93])).

fof(f2079,plain,
    ( k1_xboole_0 = sK1
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2078,f92])).

fof(f92,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f2078,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f2065,f96])).

fof(f96,plain,(
    v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f2065,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | k1_xboole_0 = sK1
    | ~ v2_pre_topc(sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 = X1
      | ~ v2_pre_topc(X0)
      | v1_compts_1(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( ( v2_compts_1(X1,X0)
                  | ~ v1_compts_1(k1_pre_topc(X0,X1)) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) ) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 = X1
              | ~ v2_pre_topc(X0) )
            & ( ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) )
              | k1_xboole_0 != X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',t12_compts_1)).

fof(f2061,plain,
    ( spl9_126
    | ~ spl9_11
    | ~ spl9_131 ),
    inference(avatar_split_clause,[],[f2060,f826,f207,f788])).

fof(f788,plain,
    ( spl9_126
  <=> v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f207,plain,
    ( spl9_11
  <=> ~ v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f826,plain,
    ( spl9_131
  <=> ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_131])])).

fof(f2060,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    inference(global_subsumption,[],[f359,f800])).

fof(f800,plain,
    ( ~ v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(resolution,[],[f794,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | v2_compts_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',t17_compts_1)).

fof(f794,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f634,f603])).

fof(f603,plain,(
    sK2 = sK3(k1_pre_topc(sK0,sK1),sK2) ),
    inference(subsumption_resolution,[],[f602,f220])).

fof(f602,plain,
    ( sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f600,f97])).

fof(f97,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f600,plain,
    ( ~ r1_tarski(sK2,sK1)
    | sK2 = sK3(k1_pre_topc(sK0,sK1),sK2)
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f277,f358])).

fof(f358,plain,(
    k2_struct_0(k1_pre_topc(sK0,sK1)) = sK1 ),
    inference(subsumption_resolution,[],[f357,f93])).

fof(f357,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f356,f94])).

fof(f356,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f354,f219])).

fof(f219,plain,(
    v1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f194,f93])).

fof(f194,plain,
    ( v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f94,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f354,plain,
    ( k2_struct_0(k1_pre_topc(sK0,sK1)) = sK1
    | ~ v1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f220,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',d10_pre_topc)).

fof(f277,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2,k2_struct_0(X1))
      | sK2 = sK3(X1,sK2)
      | ~ m1_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f276,f93])).

fof(f276,plain,(
    ! [X1] :
      ( sK2 = sK3(X1,sK2)
      | ~ r1_tarski(sK2,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f260,f99])).

fof(f260,plain,(
    ! [X1] :
      ( sK2 = sK3(X1,sK2)
      | ~ r1_tarski(sK2,k2_struct_0(X1))
      | v2_compts_1(sK2,sK0)
      | ~ m1_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f95,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sK3(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK3(X1,X2),X1)
                    & sK3(X1,X2) = X2
                    & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f78,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK3(X1,X2),X1)
        & sK3(X1,X2) = X2
        & m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',t11_compts_1)).

fof(f634,plain,(
    m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f633,f220])).

fof(f633,plain,
    ( m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f631,f97])).

fof(f631,plain,
    ( ~ r1_tarski(sK2,sK1)
    | m1_subset_1(sK3(k1_pre_topc(sK0,sK1),sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
    | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f275,f358])).

fof(f275,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f274,f93])).

fof(f274,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f259,f99])).

fof(f259,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,sK2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | v2_compts_1(sK2,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f95,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | v2_compts_1(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f359,plain,(
    l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f355,f93])).

fof(f355,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f220,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',dt_m1_pre_topc)).

fof(f1643,plain,
    ( spl9_11
    | ~ spl9_12 ),
    inference(avatar_contradiction_clause,[],[f1642])).

fof(f1642,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1620,f1615])).

fof(f1615,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1614,f93])).

fof(f1614,plain,
    ( v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f1597,f1492])).

fof(f1492,plain,
    ( v2_compts_1(k1_xboole_0,sK0)
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f217,f96])).

fof(f217,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f1597,plain,
    ( ~ v2_compts_1(k1_xboole_0,sK0)
    | v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ l1_pre_topc(sK0)
    | ~ spl9_12 ),
    inference(resolution,[],[f1491,f142])).

fof(f142,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_compts_1(k1_xboole_0,X0)
      | v1_compts_1(k1_pre_topc(X0,k1_xboole_0))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( v1_compts_1(k1_pre_topc(X0,X1))
      | ~ v2_compts_1(X1,X0)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f1491,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12 ),
    inference(backward_demodulation,[],[f217,f94])).

fof(f1620,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,k1_xboole_0))
    | ~ spl9_11
    | ~ spl9_12 ),
    inference(forward_demodulation,[],[f208,f217])).

fof(f208,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f207])).

fof(f1481,plain,(
    ~ spl9_128 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1479,f98])).

fof(f98,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f1479,plain,
    ( ~ v4_pre_topc(sK2,sK0)
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1478,f95])).

fof(f1478,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK2,sK0)
    | ~ spl9_128 ),
    inference(subsumption_resolution,[],[f1477,f93])).

fof(f1477,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(sK2,sK0)
    | ~ spl9_128 ),
    inference(resolution,[],[f824,f220])).

fof(f824,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ v4_pre_topc(sK2,X3) )
    | ~ spl9_128 ),
    inference(avatar_component_clause,[],[f823])).

fof(f823,plain,
    ( spl9_128
  <=> ! [X3] :
        ( ~ v4_pre_topc(sK2,X3)
        | ~ l1_pre_topc(X3)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_128])])).

fof(f831,plain,
    ( spl9_128
    | spl9_130 ),
    inference(avatar_split_clause,[],[f804,f829,f823])).

fof(f829,plain,
    ( spl9_130
  <=> v4_pre_topc(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f804,plain,(
    ! [X3] :
      ( v4_pre_topc(sK2,k1_pre_topc(sK0,sK1))
      | ~ v4_pre_topc(sK2,X3)
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f794,f143])).

fof(f143,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v4_pre_topc(X3,X2)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/compts_1__t18_compts_1.p',t34_tops_2)).

fof(f793,plain,
    ( spl9_124
    | ~ spl9_127 ),
    inference(avatar_split_clause,[],[f783,f791,f785])).

fof(f791,plain,
    ( spl9_127
  <=> ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_127])])).

fof(f783,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f782,f97])).

fof(f782,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,sK1)
      | ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(forward_demodulation,[],[f781,f358])).

fof(f781,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,k1_pre_topc(sK0,sK1))
      | v2_compts_1(sK2,X0)
      | ~ r1_tarski(sK2,k2_struct_0(k1_pre_topc(sK0,sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f111,f603])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK3(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f80])).
%------------------------------------------------------------------------------
