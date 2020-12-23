%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1275+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 274 expanded)
%              Number of leaves         :   10 (  74 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 (1567 expanded)
%              Number of equality atoms :   41 ( 382 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2864,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2428,f2429,f2839,f2863])).

fof(f2863,plain,
    ( ~ spl15_1
    | spl15_2 ),
    inference(avatar_contradiction_clause,[],[f2862])).

fof(f2862,plain,
    ( $false
    | ~ spl15_1
    | spl15_2 ),
    inference(subsumption_resolution,[],[f2861,f2427])).

fof(f2427,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | spl15_2 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2425,plain,
    ( spl15_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f2861,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f2860,f2702])).

fof(f2702,plain,(
    r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f2701,f2333])).

fof(f2333,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2288,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2285,f2287,f2286])).

fof(f2286,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2287,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2285,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2284])).

fof(f2284,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2222])).

fof(f2222,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2221])).

fof(f2221,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2182])).

fof(f2182,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f2181])).

fof(f2181,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f2701,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f2433,f2334])).

fof(f2334,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2433,plain,(
    ! [X3] :
      ( ~ v4_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k2_tops_1(sK0,X3),X3) ) ),
    inference(resolution,[],[f2332,f2357])).

fof(f2357,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2234])).

fof(f2234,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2233])).

fof(f2233,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2159])).

fof(f2159,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_tops_1)).

fof(f2332,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2860,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | sK1 = k2_tops_1(sK0,sK1)
    | ~ spl15_1 ),
    inference(resolution,[],[f2852,f2343])).

fof(f2343,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2294,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2293])).

fof(f2293,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f2852,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f2851,f2333])).

fof(f2851,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl15_1 ),
    inference(resolution,[],[f2849,f2431])).

fof(f2431,plain,(
    ! [X1] :
      ( ~ v2_tops_1(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X1,k2_tops_1(sK0,X1)) ) ),
    inference(resolution,[],[f2332,f2355])).

fof(f2355,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2308])).

fof(f2308,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2232])).

fof(f2232,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2176])).

fof(f2176,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f2849,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl15_1 ),
    inference(forward_demodulation,[],[f2848,f2834])).

fof(f2834,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f2833,f2333])).

fof(f2833,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f2460,f2334])).

fof(f2460,plain,(
    ! [X38] :
      ( ~ v4_pre_topc(X38,sK0)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X38) = X38 ) ),
    inference(resolution,[],[f2332,f2384])).

fof(f2384,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2259])).

fof(f2259,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2258])).

fof(f2258,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2194])).

fof(f2194,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f1843])).

fof(f1843,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f2848,plain,
    ( v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl15_1 ),
    inference(subsumption_resolution,[],[f2846,f2333])).

fof(f2846,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl15_1 ),
    inference(resolution,[],[f2422,f2443])).

fof(f2443,plain,(
    ! [X13] :
      ( ~ v3_tops_1(X13,sK0)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(k2_pre_topc(sK0,X13),sK0) ) ),
    inference(resolution,[],[f2332,f2367])).

fof(f2367,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f2309])).

fof(f2309,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2244])).

fof(f2244,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2095])).

fof(f2095,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_1)).

fof(f2422,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl15_1 ),
    inference(avatar_component_clause,[],[f2421])).

fof(f2421,plain,
    ( spl15_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f2839,plain,
    ( spl15_1
    | ~ spl15_2 ),
    inference(avatar_contradiction_clause,[],[f2838])).

fof(f2838,plain,
    ( $false
    | spl15_1
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f2837,f2423])).

fof(f2423,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | spl15_1 ),
    inference(avatar_component_clause,[],[f2421])).

fof(f2837,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f2836,f2333])).

fof(f2836,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(sK1,sK0)
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f2835,f2693])).

fof(f2693,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f2692,f2333])).

fof(f2692,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl15_2 ),
    inference(subsumption_resolution,[],[f2691,f2419])).

fof(f2419,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2341])).

fof(f2341,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2691,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tops_1(sK1,sK0)
    | ~ spl15_2 ),
    inference(superposition,[],[f2432,f2426])).

fof(f2426,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2432,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,k2_tops_1(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(X2,sK0) ) ),
    inference(resolution,[],[f2332,f2356])).

fof(f2356,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2308])).

fof(f2835,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(sK1,sK0) ),
    inference(superposition,[],[f2444,f2834])).

fof(f2444,plain,(
    ! [X14] :
      ( ~ v2_tops_1(k2_pre_topc(sK0,X14),sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_1(X14,sK0) ) ),
    inference(resolution,[],[f2332,f2368])).

fof(f2368,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f2309])).

fof(f2429,plain,
    ( spl15_1
    | spl15_2 ),
    inference(avatar_split_clause,[],[f2335,f2425,f2421])).

fof(f2335,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2288])).

fof(f2428,plain,
    ( ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f2336,f2425,f2421])).

fof(f2336,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2288])).
%------------------------------------------------------------------------------
