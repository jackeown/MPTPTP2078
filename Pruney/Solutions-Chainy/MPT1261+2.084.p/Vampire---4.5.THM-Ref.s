%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:00 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 187 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  283 ( 806 expanded)
%              Number of equality atoms :   70 ( 215 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f267,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f61,f82,f84,f116,f118,f120,f235,f237,f238,f266])).

fof(f266,plain,
    ( ~ spl2_7
    | ~ spl2_3
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f263,f113,f57,f74,f105])).

fof(f105,plain,
    ( spl2_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f74,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f113,plain,
    ( spl2_9
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f263,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_9 ),
    inference(superposition,[],[f37,f114])).

fof(f114,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f238,plain,
    ( ~ spl2_7
    | spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f88,f53,f113,f105])).

fof(f53,plain,
    ( spl2_1
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f88,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f38,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | ~ v4_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | ~ v4_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1))
          | v4_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | ~ v4_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
        | v4_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | ~ v4_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f237,plain,
    ( ~ spl2_4
    | spl2_12 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl2_4
    | spl2_12 ),
    inference(resolution,[],[f234,f87])).

fof(f87,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f48,f80])).

fof(f80,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_4
  <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f234,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl2_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl2_12
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

% (14844)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
fof(f235,plain,
    ( ~ spl2_12
    | ~ spl2_7
    | spl2_9 ),
    inference(avatar_split_clause,[],[f228,f113,f105,f232])).

fof(f228,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f227,f33])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f226])).

fof(f226,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f222,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f222,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3)))
      | k2_pre_topc(X3,X2) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(k2_tops_1(X3,X2),X2) ) ),
    inference(superposition,[],[f137,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f137,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1)))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f51,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f42])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f120,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f111,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f111,plain,
    ( ~ v2_pre_topc(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f118,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f107,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f105])).

fof(f116,plain,
    ( ~ spl2_7
    | spl2_1
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f101,f113,f109,f53,f105])).

fof(f101,plain,
    ( sK1 != k2_pre_topc(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f84,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f76,f33])).

fof(f76,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f82,plain,
    ( ~ spl2_3
    | spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f57,f78,f74])).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f58,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f58,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f61,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f34,f57,f53])).

fof(f34,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f35,f57,f53])).

fof(f35,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n023.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 16:57:51 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.37  % (14836)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.18/0.40  % (14836)Refutation found. Thanks to Tanya!
% 0.18/0.40  % SZS status Theorem for theBenchmark
% 0.18/0.40  % SZS output start Proof for theBenchmark
% 0.18/0.40  fof(f267,plain,(
% 0.18/0.40    $false),
% 0.18/0.40    inference(avatar_sat_refutation,[],[f60,f61,f82,f84,f116,f118,f120,f235,f237,f238,f266])).
% 0.18/0.40  fof(f266,plain,(
% 0.18/0.40    ~spl2_7 | ~spl2_3 | spl2_2 | ~spl2_9),
% 0.18/0.40    inference(avatar_split_clause,[],[f263,f113,f57,f74,f105])).
% 0.18/0.40  fof(f105,plain,(
% 0.18/0.40    spl2_7 <=> l1_pre_topc(sK0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.18/0.40  fof(f74,plain,(
% 0.18/0.40    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.18/0.40  fof(f57,plain,(
% 0.18/0.40    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.18/0.40  fof(f113,plain,(
% 0.18/0.40    spl2_9 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.18/0.40  fof(f263,plain,(
% 0.18/0.40    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_9),
% 0.18/0.40    inference(superposition,[],[f37,f114])).
% 0.18/0.40  fof(f114,plain,(
% 0.18/0.40    sK1 = k2_pre_topc(sK0,sK1) | ~spl2_9),
% 0.18/0.40    inference(avatar_component_clause,[],[f113])).
% 0.18/0.40  fof(f37,plain,(
% 0.18/0.40    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.40    inference(cnf_transformation,[],[f17])).
% 0.18/0.40  fof(f17,plain,(
% 0.18/0.40    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.40    inference(ennf_transformation,[],[f10])).
% 0.18/0.40  fof(f10,axiom,(
% 0.18/0.40    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.18/0.40    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 0.18/0.40  fof(f238,plain,(
% 0.18/0.40    ~spl2_7 | spl2_9 | ~spl2_1),
% 0.18/0.40    inference(avatar_split_clause,[],[f88,f53,f113,f105])).
% 0.18/0.40  fof(f53,plain,(
% 0.18/0.40    spl2_1 <=> v4_pre_topc(sK1,sK0)),
% 0.18/0.40    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.18/0.40  fof(f88,plain,(
% 0.18/0.40    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.18/0.40    inference(resolution,[],[f38,f33])).
% 0.18/0.40  fof(f33,plain,(
% 0.18/0.40    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.40    inference(cnf_transformation,[],[f30])).
% 0.18/0.40  fof(f30,plain,(
% 0.18/0.40    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.18/0.40    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f29,f28])).
% 0.18/0.41  fof(f28,plain,(
% 0.18/0.41    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f29,plain,(
% 0.18/0.41    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | ~v4_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.18/0.41    introduced(choice_axiom,[])).
% 0.18/0.41  fof(f27,plain,(
% 0.18/0.41    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.41    inference(flattening,[],[f26])).
% 0.18/0.41  fof(f26,plain,(
% 0.18/0.41    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.41    inference(nnf_transformation,[],[f15])).
% 0.18/0.41  fof(f15,plain,(
% 0.18/0.41    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.18/0.41    inference(flattening,[],[f14])).
% 0.18/0.41  fof(f14,plain,(
% 0.18/0.41    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.18/0.41    inference(ennf_transformation,[],[f13])).
% 0.18/0.41  fof(f13,negated_conjecture,(
% 0.18/0.41    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.18/0.41    inference(negated_conjecture,[],[f12])).
% 0.18/0.41  fof(f12,conjecture,(
% 0.18/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 0.18/0.41  fof(f38,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f19])).
% 0.18/0.41  fof(f19,plain,(
% 0.18/0.41    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.41    inference(flattening,[],[f18])).
% 0.18/0.41  fof(f18,plain,(
% 0.18/0.41    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.41    inference(ennf_transformation,[],[f8])).
% 0.18/0.41  fof(f8,axiom,(
% 0.18/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.18/0.41  fof(f237,plain,(
% 0.18/0.41    ~spl2_4 | spl2_12),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f236])).
% 0.18/0.41  fof(f236,plain,(
% 0.18/0.41    $false | (~spl2_4 | spl2_12)),
% 0.18/0.41    inference(resolution,[],[f234,f87])).
% 0.18/0.41  fof(f87,plain,(
% 0.18/0.41    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl2_4),
% 0.18/0.41    inference(superposition,[],[f48,f80])).
% 0.18/0.41  fof(f80,plain,(
% 0.18/0.41    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl2_4),
% 0.18/0.41    inference(avatar_component_clause,[],[f78])).
% 0.18/0.41  fof(f78,plain,(
% 0.18/0.41    spl2_4 <=> k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.18/0.41  fof(f48,plain,(
% 0.18/0.41    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f40,f43])).
% 0.18/0.41  fof(f43,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f1])).
% 0.18/0.41  fof(f1,axiom,(
% 0.18/0.41    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.18/0.41  fof(f40,plain,(
% 0.18/0.41    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f3])).
% 0.18/0.41  fof(f3,axiom,(
% 0.18/0.41    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.18/0.41  fof(f234,plain,(
% 0.18/0.41    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl2_12),
% 0.18/0.41    inference(avatar_component_clause,[],[f232])).
% 0.18/0.41  fof(f232,plain,(
% 0.18/0.41    spl2_12 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.18/0.41  % (14844)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.18/0.41  fof(f235,plain,(
% 0.18/0.41    ~spl2_12 | ~spl2_7 | spl2_9),
% 0.18/0.41    inference(avatar_split_clause,[],[f228,f113,f105,f232])).
% 0.18/0.41  fof(f228,plain,(
% 0.18/0.41    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0) | ~r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 0.18/0.41    inference(resolution,[],[f227,f33])).
% 0.18/0.41  fof(f227,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0) | ~r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 0.18/0.41    inference(duplicate_literal_removal,[],[f226])).
% 0.18/0.41  fof(f226,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(k2_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(resolution,[],[f222,f45])).
% 0.18/0.41  fof(f45,plain,(
% 0.18/0.41    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f22])).
% 0.18/0.41  fof(f22,plain,(
% 0.18/0.41    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.18/0.41    inference(flattening,[],[f21])).
% 0.18/0.41  fof(f21,plain,(
% 0.18/0.41    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.18/0.41    inference(ennf_transformation,[],[f9])).
% 0.18/0.41  fof(f9,axiom,(
% 0.18/0.41    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.18/0.41  fof(f222,plain,(
% 0.18/0.41    ( ! [X2,X3] : (~m1_subset_1(k2_tops_1(X3,X2),k1_zfmisc_1(u1_struct_0(X3))) | k2_pre_topc(X3,X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(k2_tops_1(X3,X2),X2)) )),
% 0.18/0.41    inference(superposition,[],[f137,f62])).
% 0.18/0.41  fof(f62,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_tarski(k2_tarski(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.41    inference(superposition,[],[f49,f41])).
% 0.18/0.41  fof(f41,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f4])).
% 0.18/0.41  fof(f4,axiom,(
% 0.18/0.41    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.18/0.41  fof(f49,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.41    inference(definition_unfolding,[],[f44,f42])).
% 0.18/0.41  fof(f42,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f5])).
% 0.18/0.41  fof(f5,axiom,(
% 0.18/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.18/0.41  fof(f44,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f20])).
% 0.18/0.41  fof(f20,plain,(
% 0.18/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.18/0.41    inference(ennf_transformation,[],[f2])).
% 0.18/0.41  fof(f2,axiom,(
% 0.18/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.18/0.41  fof(f137,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(duplicate_literal_removal,[],[f136])).
% 0.18/0.41  fof(f136,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k3_tarski(k2_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(superposition,[],[f51,f36])).
% 0.18/0.41  fof(f36,plain,(
% 0.18/0.41    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f16])).
% 0.18/0.41  fof(f16,plain,(
% 0.18/0.41    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.18/0.41    inference(ennf_transformation,[],[f11])).
% 0.18/0.41  fof(f11,axiom,(
% 0.18/0.41    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 0.18/0.41  fof(f51,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.41    inference(definition_unfolding,[],[f47,f42])).
% 0.18/0.41  fof(f47,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f25])).
% 0.18/0.41  fof(f25,plain,(
% 0.18/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.41    inference(flattening,[],[f24])).
% 0.18/0.41  fof(f24,plain,(
% 0.18/0.41    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.18/0.41    inference(ennf_transformation,[],[f6])).
% 0.18/0.41  fof(f6,axiom,(
% 0.18/0.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.18/0.41  fof(f120,plain,(
% 0.18/0.41    spl2_8),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f119])).
% 0.18/0.41  fof(f119,plain,(
% 0.18/0.41    $false | spl2_8),
% 0.18/0.41    inference(resolution,[],[f111,f31])).
% 0.18/0.41  fof(f31,plain,(
% 0.18/0.41    v2_pre_topc(sK0)),
% 0.18/0.41    inference(cnf_transformation,[],[f30])).
% 0.18/0.41  fof(f111,plain,(
% 0.18/0.41    ~v2_pre_topc(sK0) | spl2_8),
% 0.18/0.41    inference(avatar_component_clause,[],[f109])).
% 0.18/0.41  fof(f109,plain,(
% 0.18/0.41    spl2_8 <=> v2_pre_topc(sK0)),
% 0.18/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.18/0.41  fof(f118,plain,(
% 0.18/0.41    spl2_7),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f117])).
% 0.18/0.41  fof(f117,plain,(
% 0.18/0.41    $false | spl2_7),
% 0.18/0.41    inference(resolution,[],[f107,f32])).
% 0.18/0.41  fof(f32,plain,(
% 0.18/0.41    l1_pre_topc(sK0)),
% 0.18/0.41    inference(cnf_transformation,[],[f30])).
% 0.18/0.41  fof(f107,plain,(
% 0.18/0.41    ~l1_pre_topc(sK0) | spl2_7),
% 0.18/0.41    inference(avatar_component_clause,[],[f105])).
% 0.18/0.41  fof(f116,plain,(
% 0.18/0.41    ~spl2_7 | spl2_1 | ~spl2_8 | ~spl2_9),
% 0.18/0.41    inference(avatar_split_clause,[],[f101,f113,f109,f53,f105])).
% 0.18/0.41  fof(f101,plain,(
% 0.18/0.41    sK1 != k2_pre_topc(sK0,sK1) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.18/0.41    inference(resolution,[],[f39,f33])).
% 0.18/0.41  fof(f39,plain,(
% 0.18/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.41    inference(cnf_transformation,[],[f19])).
% 0.18/0.41  fof(f84,plain,(
% 0.18/0.41    spl2_3),
% 0.18/0.41    inference(avatar_contradiction_clause,[],[f83])).
% 0.18/0.41  fof(f83,plain,(
% 0.18/0.41    $false | spl2_3),
% 0.18/0.41    inference(resolution,[],[f76,f33])).
% 0.18/0.41  fof(f76,plain,(
% 0.18/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_3),
% 0.18/0.41    inference(avatar_component_clause,[],[f74])).
% 0.18/0.41  fof(f82,plain,(
% 0.18/0.41    ~spl2_3 | spl2_4 | ~spl2_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f71,f57,f78,f74])).
% 0.18/0.41  fof(f71,plain,(
% 0.18/0.41    k2_tops_1(sK0,sK1) = k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.18/0.41    inference(superposition,[],[f58,f50])).
% 0.18/0.41  fof(f50,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.41    inference(definition_unfolding,[],[f46,f43])).
% 0.18/0.41  fof(f46,plain,(
% 0.18/0.41    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.18/0.41    inference(cnf_transformation,[],[f23])).
% 0.18/0.41  fof(f23,plain,(
% 0.18/0.41    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.18/0.41    inference(ennf_transformation,[],[f7])).
% 0.18/0.41  fof(f7,axiom,(
% 0.18/0.41    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.18/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.18/0.41  fof(f58,plain,(
% 0.18/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl2_2),
% 0.18/0.41    inference(avatar_component_clause,[],[f57])).
% 0.18/0.41  fof(f61,plain,(
% 0.18/0.41    spl2_1 | spl2_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f34,f57,f53])).
% 0.18/0.41  fof(f34,plain,(
% 0.18/0.41    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 0.18/0.41    inference(cnf_transformation,[],[f30])).
% 0.18/0.41  fof(f60,plain,(
% 0.18/0.41    ~spl2_1 | ~spl2_2),
% 0.18/0.41    inference(avatar_split_clause,[],[f35,f57,f53])).
% 0.18/0.41  fof(f35,plain,(
% 0.18/0.41    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 0.18/0.41    inference(cnf_transformation,[],[f30])).
% 0.18/0.41  % SZS output end Proof for theBenchmark
% 0.18/0.41  % (14836)------------------------------
% 0.18/0.41  % (14836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.41  % (14836)Termination reason: Refutation
% 0.18/0.41  
% 0.18/0.41  % (14836)Memory used [KB]: 6268
% 0.18/0.41  % (14836)Time elapsed: 0.047 s
% 0.18/0.41  % (14836)------------------------------
% 0.18/0.41  % (14836)------------------------------
% 0.18/0.41  % (14831)Success in time 0.086 s
%------------------------------------------------------------------------------
