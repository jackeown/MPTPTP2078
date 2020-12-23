%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1385+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 5.69s
% Output     : Refutation 5.69s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 559 expanded)
%              Number of leaves         :   13 ( 176 expanded)
%              Depth                    :   16
%              Number of atoms          :  377 (3971 expanded)
%              Number of equality atoms :    6 (  24 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4873,f4923,f6991,f7233])).

fof(f7233,plain,
    ( ~ spl120_1
    | spl120_2 ),
    inference(avatar_contradiction_clause,[],[f7232])).

fof(f7232,plain,
    ( $false
    | ~ spl120_1
    | spl120_2 ),
    inference(subsumption_resolution,[],[f7194,f7060])).

fof(f7060,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | spl120_2 ),
    inference(subsumption_resolution,[],[f7059,f3295])).

fof(f3295,plain,(
    v2_pre_topc(sK32) ),
    inference(cnf_transformation,[],[f3008])).

fof(f3008,plain,
    ( ( ~ m1_connsp_2(sK34,sK32,sK33)
      | ~ m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
    & ( m1_connsp_2(sK34,sK32,sK33)
      | m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
    & m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32)))
    & m1_subset_1(sK33,u1_struct_0(sK32))
    & l1_pre_topc(sK32)
    & v2_pre_topc(sK32)
    & ~ v2_struct_0(sK32) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32,sK33,sK34])],[f3004,f3007,f3006,f3005])).

fof(f3005,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_connsp_2(X2,X0,X1)
                  | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & ( m1_connsp_2(X2,X0,X1)
                  | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,sK32,X1)
                | ~ m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),X1)) )
              & ( m1_connsp_2(X2,sK32,X1)
                | m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK32))) )
          & m1_subset_1(X1,u1_struct_0(sK32)) )
      & l1_pre_topc(sK32)
      & v2_pre_topc(sK32)
      & ~ v2_struct_0(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f3006,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ m1_connsp_2(X2,sK32,X1)
              | ~ m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),X1)) )
            & ( m1_connsp_2(X2,sK32,X1)
              | m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),X1)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK32))) )
        & m1_subset_1(X1,u1_struct_0(sK32)) )
   => ( ? [X2] :
          ( ( ~ m1_connsp_2(X2,sK32,sK33)
            | ~ m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
          & ( m1_connsp_2(X2,sK32,sK33)
            | m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK32))) )
      & m1_subset_1(sK33,u1_struct_0(sK32)) ) ),
    introduced(choice_axiom,[])).

fof(f3007,plain,
    ( ? [X2] :
        ( ( ~ m1_connsp_2(X2,sK32,sK33)
          | ~ m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
        & ( m1_connsp_2(X2,sK32,sK33)
          | m2_connsp_2(X2,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK32))) )
   => ( ( ~ m1_connsp_2(sK34,sK32,sK33)
        | ~ m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
      & ( m1_connsp_2(sK34,sK32,sK33)
        | m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) )
      & m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32))) ) ),
    introduced(choice_axiom,[])).

fof(f3004,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3003])).

fof(f3003,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_connsp_2(X2,X0,X1)
                | ~ m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & ( m1_connsp_2(X2,X0,X1)
                | m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2544])).

fof(f2544,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2543])).

fof(f2543,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <~> m1_connsp_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2523])).

fof(f2523,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
                <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f2522])).

fof(f2522,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,k6_domain_1(u1_struct_0(X0),X1))
              <=> m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_connsp_2)).

fof(f7059,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ v2_pre_topc(sK32)
    | spl120_2 ),
    inference(subsumption_resolution,[],[f7058,f3296])).

fof(f3296,plain,(
    l1_pre_topc(sK32) ),
    inference(cnf_transformation,[],[f3008])).

fof(f7058,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | spl120_2 ),
    inference(subsumption_resolution,[],[f7057,f4310])).

fof(f4310,plain,(
    m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(backward_demodulation,[],[f4308,f4309])).

fof(f4309,plain,(
    k6_domain_1(u1_struct_0(sK32),sK33) = k1_tarski(sK33) ),
    inference(global_subsumption,[],[f3938,f4227,f4255])).

fof(f4255,plain,
    ( k6_domain_1(u1_struct_0(sK32),sK33) = k1_tarski(sK33)
    | v1_xboole_0(u1_struct_0(sK32)) ),
    inference(resolution,[],[f3297,f3339])).

fof(f3339,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2574])).

fof(f2574,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2573])).

fof(f2573,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1935])).

fof(f1935,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f3297,plain,(
    m1_subset_1(sK33,u1_struct_0(sK32)) ),
    inference(cnf_transformation,[],[f3008])).

fof(f4227,plain,(
    l1_struct_0(sK32) ),
    inference(resolution,[],[f3296,f3842])).

fof(f3842,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2917])).

fof(f2917,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3938,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK32))
    | ~ l1_struct_0(sK32) ),
    inference(resolution,[],[f3294,f3840])).

fof(f3840,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2914])).

fof(f2914,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2913])).

fof(f2913,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f3294,plain,(
    ~ v2_struct_0(sK32) ),
    inference(cnf_transformation,[],[f3008])).

fof(f4308,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK32),sK33),k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(global_subsumption,[],[f3938,f4227,f4254])).

fof(f4254,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK32),sK33),k1_zfmisc_1(u1_struct_0(sK32)))
    | v1_xboole_0(u1_struct_0(sK32)) ),
    inference(resolution,[],[f3297,f3338])).

fof(f3338,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2572])).

fof(f2572,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f2571])).

fof(f2571,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1893])).

fof(f1893,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f7057,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | spl120_2 ),
    inference(subsumption_resolution,[],[f7042,f3298])).

fof(f3298,plain,(
    m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32))) ),
    inference(cnf_transformation,[],[f3008])).

fof(f7042,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | spl120_2 ),
    inference(resolution,[],[f4922,f3337])).

fof(f3337,plain,(
    ! [X2,X0,X1] :
      ( m2_connsp_2(X2,X0,X1)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3032])).

fof(f3032,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2570])).

fof(f2570,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2569])).

fof(f2569,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2515])).

fof(f2515,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f4922,plain,
    ( ~ m2_connsp_2(sK34,sK32,k1_tarski(sK33))
    | spl120_2 ),
    inference(avatar_component_clause,[],[f4871])).

fof(f4871,plain,
    ( spl120_2
  <=> m2_connsp_2(sK34,sK32,k1_tarski(sK33)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl120_2])])).

fof(f7194,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ spl120_1 ),
    inference(resolution,[],[f7041,f3507])).

fof(f3507,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3133])).

fof(f3133,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f7041,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ spl120_1 ),
    inference(subsumption_resolution,[],[f7040,f3294])).

fof(f7040,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | v2_struct_0(sK32)
    | ~ spl120_1 ),
    inference(subsumption_resolution,[],[f7039,f3295])).

fof(f7039,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | ~ spl120_1 ),
    inference(subsumption_resolution,[],[f7038,f3296])).

fof(f7038,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | ~ spl120_1 ),
    inference(subsumption_resolution,[],[f7037,f3297])).

fof(f7037,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK33,u1_struct_0(sK32))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | ~ spl120_1 ),
    inference(subsumption_resolution,[],[f7000,f3298])).

fof(f7000,plain,
    ( r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ m1_subset_1(sK33,u1_struct_0(sK32))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | ~ spl120_1 ),
    inference(resolution,[],[f4869,f3332])).

fof(f3332,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3029])).

fof(f3029,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2564])).

fof(f2564,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2563])).

fof(f2563,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2514])).

fof(f2514,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f4869,plain,
    ( m1_connsp_2(sK34,sK32,sK33)
    | ~ spl120_1 ),
    inference(avatar_component_clause,[],[f4868])).

fof(f4868,plain,
    ( spl120_1
  <=> m1_connsp_2(sK34,sK32,sK33) ),
    introduced(avatar_definition,[new_symbols(naming,[spl120_1])])).

fof(f6991,plain,
    ( spl120_1
    | ~ spl120_2 ),
    inference(avatar_contradiction_clause,[],[f6990])).

fof(f6990,plain,
    ( $false
    | spl120_1
    | ~ spl120_2 ),
    inference(subsumption_resolution,[],[f6968,f4916])).

fof(f4916,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ spl120_2 ),
    inference(subsumption_resolution,[],[f4915,f3295])).

fof(f4915,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ v2_pre_topc(sK32)
    | ~ spl120_2 ),
    inference(subsumption_resolution,[],[f4914,f3296])).

fof(f4914,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | ~ spl120_2 ),
    inference(subsumption_resolution,[],[f4913,f4310])).

fof(f4913,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | ~ spl120_2 ),
    inference(subsumption_resolution,[],[f4897,f3298])).

fof(f4897,plain,
    ( r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ m1_subset_1(k1_tarski(sK33),k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | ~ spl120_2 ),
    inference(resolution,[],[f4872,f3336])).

fof(f3336,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3032])).

fof(f4872,plain,
    ( m2_connsp_2(sK34,sK32,k1_tarski(sK33))
    | ~ spl120_2 ),
    inference(avatar_component_clause,[],[f4871])).

fof(f6968,plain,
    ( ~ r1_tarski(k1_tarski(sK33),k1_tops_1(sK32,sK34))
    | spl120_1 ),
    inference(resolution,[],[f4933,f3506])).

fof(f3506,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3133])).

fof(f4933,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | spl120_1 ),
    inference(subsumption_resolution,[],[f4932,f3294])).

fof(f4932,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | v2_struct_0(sK32)
    | spl120_1 ),
    inference(subsumption_resolution,[],[f4931,f3295])).

fof(f4931,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | spl120_1 ),
    inference(subsumption_resolution,[],[f4930,f3296])).

fof(f4930,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | spl120_1 ),
    inference(subsumption_resolution,[],[f4929,f3297])).

fof(f4929,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK33,u1_struct_0(sK32))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | spl120_1 ),
    inference(subsumption_resolution,[],[f4924,f3298])).

fof(f4924,plain,
    ( ~ r2_hidden(sK33,k1_tops_1(sK32,sK34))
    | ~ m1_subset_1(sK34,k1_zfmisc_1(u1_struct_0(sK32)))
    | ~ m1_subset_1(sK33,u1_struct_0(sK32))
    | ~ l1_pre_topc(sK32)
    | ~ v2_pre_topc(sK32)
    | v2_struct_0(sK32)
    | spl120_1 ),
    inference(resolution,[],[f4921,f3333])).

fof(f3333,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3029])).

fof(f4921,plain,
    ( ~ m1_connsp_2(sK34,sK32,sK33)
    | spl120_1 ),
    inference(avatar_component_clause,[],[f4868])).

fof(f4923,plain,
    ( ~ spl120_1
    | ~ spl120_2 ),
    inference(avatar_split_clause,[],[f4312,f4871,f4868])).

fof(f4312,plain,
    ( ~ m2_connsp_2(sK34,sK32,k1_tarski(sK33))
    | ~ m1_connsp_2(sK34,sK32,sK33) ),
    inference(backward_demodulation,[],[f3300,f4309])).

fof(f3300,plain,
    ( ~ m1_connsp_2(sK34,sK32,sK33)
    | ~ m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) ),
    inference(cnf_transformation,[],[f3008])).

fof(f4873,plain,
    ( spl120_1
    | spl120_2 ),
    inference(avatar_split_clause,[],[f4311,f4871,f4868])).

fof(f4311,plain,
    ( m2_connsp_2(sK34,sK32,k1_tarski(sK33))
    | m1_connsp_2(sK34,sK32,sK33) ),
    inference(backward_demodulation,[],[f3299,f4309])).

fof(f3299,plain,
    ( m1_connsp_2(sK34,sK32,sK33)
    | m2_connsp_2(sK34,sK32,k6_domain_1(u1_struct_0(sK32),sK33)) ),
    inference(cnf_transformation,[],[f3008])).
%------------------------------------------------------------------------------
