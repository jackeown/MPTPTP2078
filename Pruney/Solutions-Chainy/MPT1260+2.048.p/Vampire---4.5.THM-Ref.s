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
% DateTime   : Thu Dec  3 13:11:41 EST 2020

% Result     : Theorem 2.85s
% Output     : Refutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 583 expanded)
%              Number of leaves         :   27 ( 159 expanded)
%              Depth                    :   28
%              Number of atoms          :  380 (2923 expanded)
%              Number of equality atoms :   97 ( 804 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f2376,f5021,f5225,f5243])).

fof(f5243,plain,
    ( spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f5242])).

fof(f5242,plain,
    ( $false
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f5229,f173])).

fof(f173,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f5229,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f153,f2371])).

fof(f2371,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f2369])).

fof(f2369,plain,
    ( spl3_9
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f153,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f138,f84])).

fof(f84,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f72,f74,f73])).

fof(f73,plain,
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

fof(f74,plain,
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

fof(f72,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f39])).

fof(f39,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f138,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f75])).

fof(f5225,plain,
    ( ~ spl3_1
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f5224])).

fof(f5224,plain,
    ( $false
    | ~ spl3_1
    | spl3_10 ),
    inference(subsumption_resolution,[],[f5223,f85])).

fof(f5223,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_10 ),
    inference(subsumption_resolution,[],[f5210,f134])).

fof(f134,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
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

fof(f5210,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | spl3_10 ),
    inference(resolution,[],[f5027,f2375])).

fof(f2375,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f2373])).

fof(f2373,plain,
    ( spl3_10
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f5027,plain,
    ( ! [X0] :
        ( r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f5026,f84])).

fof(f5026,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f5025,f85])).

fof(f5025,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f170,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
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

fof(f170,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f5021,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f5020])).

fof(f5020,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f5019,f83])).

fof(f83,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f5019,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f5018,f84])).

fof(f5018,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f5017,f85])).

fof(f5017,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f5006,f201])).

fof(f201,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f87,f174])).

fof(f174,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f172])).

fof(f87,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f75])).

fof(f5006,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f103,f4921])).

fof(f4921,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f422,f4893])).

fof(f4893,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f4368,f4889])).

fof(f4889,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f404,f174])).

fof(f404,plain,(
    ! [X0] : k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) ),
    inference(resolution,[],[f382,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f382,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f381,f85])).

fof(f381,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f379,f325])).

fof(f325,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f252,f324])).

fof(f324,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f323,f84])).

fof(f323,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f101,f308])).

fof(f308,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f150,f140])).

fof(f140,plain,(
    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f85,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f150,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f135,f84])).

fof(f135,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f252,plain,(
    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f248,f85])).

fof(f248,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f116,f140])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f379,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f124,f151])).

fof(f151,plain,(
    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f84])).

fof(f136,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f124,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f4368,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f4304,f118])).

fof(f118,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f4304,plain,(
    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)) ),
    inference(superposition,[],[f3851,f418])).

fof(f418,plain,(
    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f407,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f407,plain,(
    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f382,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3851,plain,(
    ! [X1] : k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k4_xboole_0(sK1,k4_xboole_0(X1,sK1)) ),
    inference(forward_demodulation,[],[f165,f371])).

fof(f371,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f130,f350])).

fof(f350,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f149,f146])).

fof(f146,plain,(
    ! [X3] : k9_subset_1(u1_struct_0(sK0),X3,X3) = X3 ),
    inference(resolution,[],[f85,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X1) = X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f149,plain,(
    ! [X6] : k9_subset_1(u1_struct_0(sK0),X6,sK1) = k4_xboole_0(X6,k4_xboole_0(X6,sK1)) ),
    inference(resolution,[],[f85,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f119,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f130,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f117,f94])).

fof(f117,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f165,plain,(
    ! [X1] : k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X1),sK1) ),
    inference(forward_demodulation,[],[f162,f118])).

fof(f162,plain,(
    ! [X1] : k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f130,f155])).

fof(f155,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f144,f110])).

fof(f144,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f85,f105])).

fof(f422,plain,(
    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[],[f152,f141])).

fof(f141,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(resolution,[],[f85,f96])).

fof(f152,plain,(
    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f137,f84])).

fof(f137,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f85,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f2376,plain,
    ( spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f755,f2373,f2369])).

fof(f755,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f748,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f77])).

fof(f748,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[],[f114,f422])).

fof(f114,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f175,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f86,f172,f168])).

fof(f86,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:23:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (21911)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.50  % (21916)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (21935)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (21917)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (21924)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (21909)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (21936)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.52  % (21913)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (21932)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (21914)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (21919)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (21933)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (21923)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (21921)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (21918)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (21929)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (21931)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (21915)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (21912)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (21938)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (21910)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (21930)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (21934)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (21925)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (21927)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (21937)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (21926)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (21928)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (21922)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (21920)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.85/0.75  % (21933)Refutation found. Thanks to Tanya!
% 2.85/0.75  % SZS status Theorem for theBenchmark
% 2.85/0.77  % SZS output start Proof for theBenchmark
% 2.85/0.77  fof(f5245,plain,(
% 2.85/0.77    $false),
% 2.85/0.77    inference(avatar_sat_refutation,[],[f175,f2376,f5021,f5225,f5243])).
% 2.85/0.77  fof(f5243,plain,(
% 2.85/0.77    spl3_2 | ~spl3_9),
% 2.85/0.77    inference(avatar_contradiction_clause,[],[f5242])).
% 2.85/0.77  fof(f5242,plain,(
% 2.85/0.77    $false | (spl3_2 | ~spl3_9)),
% 2.85/0.77    inference(subsumption_resolution,[],[f5229,f173])).
% 2.85/0.77  fof(f173,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 2.85/0.77    inference(avatar_component_clause,[],[f172])).
% 2.85/0.77  fof(f172,plain,(
% 2.85/0.77    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.85/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.85/0.77  fof(f5229,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_9),
% 2.85/0.77    inference(backward_demodulation,[],[f153,f2371])).
% 2.85/0.77  fof(f2371,plain,(
% 2.85/0.77    sK1 = k1_tops_1(sK0,sK1) | ~spl3_9),
% 2.85/0.77    inference(avatar_component_clause,[],[f2369])).
% 2.85/0.77  fof(f2369,plain,(
% 2.85/0.77    spl3_9 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.85/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.85/0.77  fof(f153,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.85/0.77    inference(subsumption_resolution,[],[f138,f84])).
% 2.85/0.77  fof(f84,plain,(
% 2.85/0.77    l1_pre_topc(sK0)),
% 2.85/0.77    inference(cnf_transformation,[],[f75])).
% 2.85/0.77  fof(f75,plain,(
% 2.85/0.77    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.85/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f72,f74,f73])).
% 2.85/0.77  fof(f73,plain,(
% 2.85/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.85/0.77    introduced(choice_axiom,[])).
% 2.85/0.77  fof(f74,plain,(
% 2.85/0.77    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.85/0.77    introduced(choice_axiom,[])).
% 2.85/0.77  fof(f72,plain,(
% 2.85/0.77    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.85/0.77    inference(flattening,[],[f71])).
% 2.85/0.77  fof(f71,plain,(
% 2.85/0.77    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.85/0.77    inference(nnf_transformation,[],[f42])).
% 2.85/0.77  fof(f42,plain,(
% 2.85/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.85/0.77    inference(flattening,[],[f41])).
% 2.85/0.77  fof(f41,plain,(
% 2.85/0.77    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f40])).
% 2.85/0.77  fof(f40,negated_conjecture,(
% 2.85/0.77    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.85/0.77    inference(negated_conjecture,[],[f39])).
% 2.85/0.77  fof(f39,conjecture,(
% 2.85/0.77    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.85/0.77  fof(f138,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.85/0.77    inference(resolution,[],[f85,f98])).
% 2.85/0.77  fof(f98,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f48])).
% 2.85/0.77  fof(f48,plain,(
% 2.85/0.77    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(ennf_transformation,[],[f34])).
% 2.85/0.77  fof(f34,axiom,(
% 2.85/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.85/0.77  fof(f85,plain,(
% 2.85/0.77    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(cnf_transformation,[],[f75])).
% 2.85/0.77  fof(f5225,plain,(
% 2.85/0.77    ~spl3_1 | spl3_10),
% 2.85/0.77    inference(avatar_contradiction_clause,[],[f5224])).
% 2.85/0.77  fof(f5224,plain,(
% 2.85/0.77    $false | (~spl3_1 | spl3_10)),
% 2.85/0.77    inference(subsumption_resolution,[],[f5223,f85])).
% 2.85/0.77  fof(f5223,plain,(
% 2.85/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_10)),
% 2.85/0.77    inference(subsumption_resolution,[],[f5210,f134])).
% 2.85/0.77  fof(f134,plain,(
% 2.85/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.85/0.77    inference(equality_resolution,[],[f88])).
% 2.85/0.77  fof(f88,plain,(
% 2.85/0.77    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.85/0.77    inference(cnf_transformation,[],[f77])).
% 2.85/0.77  fof(f77,plain,(
% 2.85/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.85/0.77    inference(flattening,[],[f76])).
% 2.85/0.77  fof(f76,plain,(
% 2.85/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.85/0.77    inference(nnf_transformation,[],[f2])).
% 2.85/0.77  fof(f2,axiom,(
% 2.85/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.85/0.77  fof(f5210,plain,(
% 2.85/0.77    ~r1_tarski(sK1,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | spl3_10)),
% 2.85/0.77    inference(resolution,[],[f5027,f2375])).
% 2.85/0.77  fof(f2375,plain,(
% 2.85/0.77    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_10),
% 2.85/0.77    inference(avatar_component_clause,[],[f2373])).
% 2.85/0.77  fof(f2373,plain,(
% 2.85/0.77    spl3_10 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.85/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.85/0.77  fof(f5027,plain,(
% 2.85/0.77    ( ! [X0] : (r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 2.85/0.77    inference(subsumption_resolution,[],[f5026,f84])).
% 2.85/0.77  fof(f5026,plain,(
% 2.85/0.77    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_1),
% 2.85/0.77    inference(subsumption_resolution,[],[f5025,f85])).
% 2.85/0.77  fof(f5025,plain,(
% 2.85/0.77    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_1),
% 2.85/0.77    inference(resolution,[],[f170,f104])).
% 2.85/0.77  fof(f104,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f57])).
% 2.85/0.77  fof(f57,plain,(
% 2.85/0.77    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(flattening,[],[f56])).
% 2.85/0.77  fof(f56,plain,(
% 2.85/0.77    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(ennf_transformation,[],[f35])).
% 2.85/0.77  fof(f35,axiom,(
% 2.85/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 2.85/0.77  fof(f170,plain,(
% 2.85/0.77    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 2.85/0.77    inference(avatar_component_clause,[],[f168])).
% 2.85/0.77  fof(f168,plain,(
% 2.85/0.77    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 2.85/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.85/0.77  fof(f5021,plain,(
% 2.85/0.77    ~spl3_2),
% 2.85/0.77    inference(avatar_contradiction_clause,[],[f5020])).
% 2.85/0.77  fof(f5020,plain,(
% 2.85/0.77    $false | ~spl3_2),
% 2.85/0.77    inference(subsumption_resolution,[],[f5019,f83])).
% 2.85/0.77  fof(f83,plain,(
% 2.85/0.77    v2_pre_topc(sK0)),
% 2.85/0.77    inference(cnf_transformation,[],[f75])).
% 2.85/0.77  fof(f5019,plain,(
% 2.85/0.77    ~v2_pre_topc(sK0) | ~spl3_2),
% 2.85/0.77    inference(subsumption_resolution,[],[f5018,f84])).
% 2.85/0.77  fof(f5018,plain,(
% 2.85/0.77    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_2),
% 2.85/0.77    inference(subsumption_resolution,[],[f5017,f85])).
% 2.85/0.77  fof(f5017,plain,(
% 2.85/0.77    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_2),
% 2.85/0.77    inference(subsumption_resolution,[],[f5006,f201])).
% 2.85/0.77  fof(f201,plain,(
% 2.85/0.77    ~v3_pre_topc(sK1,sK0) | ~spl3_2),
% 2.85/0.77    inference(subsumption_resolution,[],[f87,f174])).
% 2.85/0.77  fof(f174,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 2.85/0.77    inference(avatar_component_clause,[],[f172])).
% 2.85/0.77  fof(f87,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.85/0.77    inference(cnf_transformation,[],[f75])).
% 2.85/0.77  fof(f5006,plain,(
% 2.85/0.77    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_2),
% 2.85/0.77    inference(superposition,[],[f103,f4921])).
% 2.85/0.77  fof(f4921,plain,(
% 2.85/0.77    sK1 = k1_tops_1(sK0,sK1) | ~spl3_2),
% 2.85/0.77    inference(backward_demodulation,[],[f422,f4893])).
% 2.85/0.77  fof(f4893,plain,(
% 2.85/0.77    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_2),
% 2.85/0.77    inference(backward_demodulation,[],[f4368,f4889])).
% 2.85/0.77  fof(f4889,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 2.85/0.77    inference(superposition,[],[f404,f174])).
% 2.85/0.77  fof(f404,plain,(
% 2.85/0.77    ( ! [X0] : (k4_xboole_0(k2_pre_topc(sK0,sK1),X0) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0)) )),
% 2.85/0.77    inference(resolution,[],[f382,f96])).
% 2.85/0.77  fof(f96,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f46])).
% 2.85/0.77  fof(f46,plain,(
% 2.85/0.77    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f22])).
% 2.85/0.77  fof(f22,axiom,(
% 2.85/0.77    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.85/0.77  fof(f382,plain,(
% 2.85/0.77    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(subsumption_resolution,[],[f381,f85])).
% 2.85/0.77  fof(f381,plain,(
% 2.85/0.77    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(subsumption_resolution,[],[f379,f325])).
% 2.85/0.77  fof(f325,plain,(
% 2.85/0.77    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(global_subsumption,[],[f252,f324])).
% 2.85/0.77  fof(f324,plain,(
% 2.85/0.77    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(subsumption_resolution,[],[f323,f84])).
% 2.85/0.77  fof(f323,plain,(
% 2.85/0.77    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.85/0.77    inference(superposition,[],[f101,f308])).
% 2.85/0.77  fof(f308,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 2.85/0.77    inference(forward_demodulation,[],[f150,f140])).
% 2.85/0.77  fof(f140,plain,(
% 2.85/0.77    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 2.85/0.77    inference(resolution,[],[f85,f92])).
% 2.85/0.77  fof(f92,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f44])).
% 2.85/0.77  fof(f44,plain,(
% 2.85/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f13])).
% 2.85/0.77  fof(f13,axiom,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.85/0.77  fof(f150,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.85/0.77    inference(subsumption_resolution,[],[f135,f84])).
% 2.85/0.77  fof(f135,plain,(
% 2.85/0.77    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 2.85/0.77    inference(resolution,[],[f85,f102])).
% 2.85/0.77  fof(f102,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~l1_pre_topc(X0)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f53])).
% 2.85/0.77  fof(f53,plain,(
% 2.85/0.77    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(ennf_transformation,[],[f36])).
% 2.85/0.77  fof(f36,axiom,(
% 2.85/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 2.85/0.77  fof(f101,plain,(
% 2.85/0.77    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f52])).
% 2.85/0.77  fof(f52,plain,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(flattening,[],[f51])).
% 2.85/0.77  fof(f51,plain,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f32])).
% 2.85/0.77  fof(f32,axiom,(
% 2.85/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.85/0.77  fof(f252,plain,(
% 2.85/0.77    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(subsumption_resolution,[],[f248,f85])).
% 2.85/0.77  fof(f248,plain,(
% 2.85/0.77    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(superposition,[],[f116,f140])).
% 2.85/0.77  fof(f116,plain,(
% 2.85/0.77    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.85/0.77    inference(cnf_transformation,[],[f63])).
% 2.85/0.77  fof(f63,plain,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f15])).
% 2.85/0.77  fof(f15,axiom,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.85/0.77  fof(f379,plain,(
% 2.85/0.77    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.85/0.77    inference(superposition,[],[f124,f151])).
% 2.85/0.77  fof(f151,plain,(
% 2.85/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.85/0.77    inference(subsumption_resolution,[],[f136,f84])).
% 2.85/0.77  fof(f136,plain,(
% 2.85/0.77    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 2.85/0.77    inference(resolution,[],[f85,f100])).
% 2.85/0.77  fof(f100,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f50])).
% 2.85/0.77  fof(f50,plain,(
% 2.85/0.77    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/0.77    inference(ennf_transformation,[],[f37])).
% 2.85/0.77  fof(f37,axiom,(
% 2.85/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.85/0.77  fof(f124,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.85/0.77    inference(cnf_transformation,[],[f70])).
% 2.85/0.77  fof(f70,plain,(
% 2.85/0.77    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(flattening,[],[f69])).
% 2.85/0.77  fof(f69,plain,(
% 2.85/0.77    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.85/0.77    inference(ennf_transformation,[],[f16])).
% 2.85/0.77  fof(f16,axiom,(
% 2.85/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.85/0.77  fof(f4368,plain,(
% 2.85/0.77    sK1 = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 2.85/0.77    inference(forward_demodulation,[],[f4304,f118])).
% 2.85/0.77  fof(f118,plain,(
% 2.85/0.77    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.85/0.77    inference(cnf_transformation,[],[f9])).
% 2.85/0.77  fof(f9,axiom,(
% 2.85/0.77    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.85/0.77  fof(f4304,plain,(
% 2.85/0.77    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(k2_pre_topc(sK0,sK1),sK1))),
% 2.85/0.77    inference(superposition,[],[f3851,f418])).
% 2.85/0.77  fof(f418,plain,(
% 2.85/0.77    k1_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 2.85/0.77    inference(resolution,[],[f407,f110])).
% 2.85/0.77  fof(f110,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.85/0.77    inference(cnf_transformation,[],[f81])).
% 2.85/0.77  fof(f81,plain,(
% 2.85/0.77    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.85/0.77    inference(nnf_transformation,[],[f3])).
% 2.85/0.77  fof(f3,axiom,(
% 2.85/0.77    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.85/0.77  fof(f407,plain,(
% 2.85/0.77    r1_tarski(k2_pre_topc(sK0,sK1),u1_struct_0(sK0))),
% 2.85/0.77    inference(resolution,[],[f382,f105])).
% 2.85/0.77  fof(f105,plain,(
% 2.85/0.77    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.85/0.77    inference(cnf_transformation,[],[f78])).
% 2.85/0.77  fof(f78,plain,(
% 2.85/0.77    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.85/0.77    inference(nnf_transformation,[],[f30])).
% 2.85/0.77  fof(f30,axiom,(
% 2.85/0.77    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.85/0.77  fof(f3851,plain,(
% 2.85/0.77    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k4_xboole_0(sK1,k4_xboole_0(X1,sK1))) )),
% 2.85/0.77    inference(forward_demodulation,[],[f165,f371])).
% 2.85/0.77  fof(f371,plain,(
% 2.85/0.77    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK1,X0),sK1) = k4_xboole_0(sK1,k4_xboole_0(X0,sK1))) )),
% 2.85/0.77    inference(superposition,[],[f130,f350])).
% 2.85/0.77  fof(f350,plain,(
% 2.85/0.77    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))),
% 2.85/0.77    inference(superposition,[],[f149,f146])).
% 2.85/0.77  fof(f146,plain,(
% 2.85/0.77    ( ! [X3] : (k9_subset_1(u1_struct_0(sK0),X3,X3) = X3) )),
% 2.85/0.77    inference(resolution,[],[f85,f122])).
% 2.85/0.77  fof(f122,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X1) = X1) )),
% 2.85/0.77    inference(cnf_transformation,[],[f66])).
% 2.85/0.77  fof(f66,plain,(
% 2.85/0.77    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f19])).
% 2.85/0.77  fof(f19,axiom,(
% 2.85/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 2.85/0.77  fof(f149,plain,(
% 2.85/0.77    ( ! [X6] : (k9_subset_1(u1_struct_0(sK0),X6,sK1) = k4_xboole_0(X6,k4_xboole_0(X6,sK1))) )),
% 2.85/0.77    inference(resolution,[],[f85,f131])).
% 2.85/0.77  fof(f131,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.85/0.77    inference(definition_unfolding,[],[f119,f94])).
% 2.85/0.77  fof(f94,plain,(
% 2.85/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.85/0.77    inference(cnf_transformation,[],[f10])).
% 2.85/0.77  fof(f10,axiom,(
% 2.85/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.85/0.77  fof(f119,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.85/0.77    inference(cnf_transformation,[],[f64])).
% 2.85/0.77  fof(f64,plain,(
% 2.85/0.77    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.85/0.77    inference(ennf_transformation,[],[f23])).
% 2.85/0.77  fof(f23,axiom,(
% 2.85/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.85/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.85/0.77  fof(f130,plain,(
% 2.85/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.85/0.77    inference(definition_unfolding,[],[f117,f94])).
% 3.22/0.77  fof(f117,plain,(
% 3.22/0.77    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.22/0.77    inference(cnf_transformation,[],[f11])).
% 3.22/0.77  fof(f11,axiom,(
% 3.22/0.77    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.22/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 3.22/0.77  fof(f165,plain,(
% 3.22/0.77    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X1),sK1)) )),
% 3.22/0.77    inference(forward_demodulation,[],[f162,f118])).
% 3.22/0.77  fof(f162,plain,(
% 3.22/0.77    ( ! [X1] : (k4_xboole_0(sK1,k4_xboole_0(X1,u1_struct_0(sK0))) = k2_xboole_0(k4_xboole_0(sK1,X1),k4_xboole_0(sK1,k1_xboole_0))) )),
% 3.22/0.77    inference(superposition,[],[f130,f155])).
% 3.22/0.77  fof(f155,plain,(
% 3.22/0.77    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))),
% 3.22/0.77    inference(resolution,[],[f144,f110])).
% 3.22/0.77  fof(f144,plain,(
% 3.22/0.77    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.22/0.77    inference(resolution,[],[f85,f105])).
% 3.22/0.77  fof(f422,plain,(
% 3.22/0.77    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.77    inference(superposition,[],[f152,f141])).
% 3.22/0.77  fof(f141,plain,(
% 3.22/0.77    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) )),
% 3.22/0.77    inference(resolution,[],[f85,f96])).
% 3.22/0.77  fof(f152,plain,(
% 3.22/0.77    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.22/0.77    inference(subsumption_resolution,[],[f137,f84])).
% 3.22/0.77  fof(f137,plain,(
% 3.22/0.77    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 3.22/0.77    inference(resolution,[],[f85,f99])).
% 3.22/0.77  fof(f99,plain,(
% 3.22/0.77    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 3.22/0.77    inference(cnf_transformation,[],[f49])).
% 3.22/0.77  fof(f49,plain,(
% 3.22/0.77    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.22/0.77    inference(ennf_transformation,[],[f38])).
% 3.22/0.77  fof(f38,axiom,(
% 3.22/0.77    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.22/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.22/0.77  fof(f103,plain,(
% 3.22/0.77    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.22/0.77    inference(cnf_transformation,[],[f55])).
% 3.22/0.77  fof(f55,plain,(
% 3.22/0.77    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.22/0.77    inference(flattening,[],[f54])).
% 3.22/0.77  fof(f54,plain,(
% 3.22/0.77    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.22/0.77    inference(ennf_transformation,[],[f33])).
% 3.22/0.77  fof(f33,axiom,(
% 3.22/0.77    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.22/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.22/0.77  fof(f2376,plain,(
% 3.22/0.77    spl3_9 | ~spl3_10),
% 3.22/0.77    inference(avatar_split_clause,[],[f755,f2373,f2369])).
% 3.22/0.77  fof(f755,plain,(
% 3.22/0.77    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1)),
% 3.22/0.77    inference(resolution,[],[f748,f90])).
% 3.22/0.77  fof(f90,plain,(
% 3.22/0.77    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.22/0.77    inference(cnf_transformation,[],[f77])).
% 3.22/0.77  fof(f748,plain,(
% 3.22/0.77    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.22/0.77    inference(superposition,[],[f114,f422])).
% 3.22/0.77  fof(f114,plain,(
% 3.22/0.77    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.22/0.77    inference(cnf_transformation,[],[f8])).
% 3.22/0.77  fof(f8,axiom,(
% 3.22/0.77    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.22/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.22/0.77  fof(f175,plain,(
% 3.22/0.77    spl3_1 | spl3_2),
% 3.22/0.77    inference(avatar_split_clause,[],[f86,f172,f168])).
% 3.22/0.77  fof(f86,plain,(
% 3.22/0.77    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.22/0.77    inference(cnf_transformation,[],[f75])).
% 3.22/0.77  % SZS output end Proof for theBenchmark
% 3.22/0.77  % (21933)------------------------------
% 3.22/0.77  % (21933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.78  % (21933)Termination reason: Refutation
% 3.22/0.78  
% 3.22/0.78  % (21933)Memory used [KB]: 13944
% 3.22/0.78  % (21933)Time elapsed: 0.340 s
% 3.22/0.78  % (21933)------------------------------
% 3.22/0.78  % (21933)------------------------------
% 3.22/0.78  % (21908)Success in time 0.425 s
%------------------------------------------------------------------------------
