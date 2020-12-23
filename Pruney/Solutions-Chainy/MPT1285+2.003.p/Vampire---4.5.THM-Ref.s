%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:05 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 612 expanded)
%              Number of leaves         :   26 ( 255 expanded)
%              Depth                    :   18
%              Number of atoms          :  552 (5783 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f111,f112,f583,f627,f657,f1577,f1662])).

fof(f1662,plain,
    ( spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f1661])).

fof(f1661,plain,
    ( $false
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1651,f120])).

fof(f120,plain,(
    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( ( ~ v4_tops_1(sK2,sK0)
          | ~ v3_pre_topc(sK2,sK0) )
        & v6_tops_1(sK2,sK0) )
      | ( ~ v6_tops_1(sK3,sK1)
        & v4_tops_1(sK3,sK1)
        & v3_pre_topc(sK3,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( ~ v4_tops_1(X2,X0)
                          | ~ v3_pre_topc(X2,X0) )
                        & v6_tops_1(X2,X0) )
                      | ( ~ v6_tops_1(X3,X1)
                        & v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,sK0)
                        | ~ v3_pre_topc(X2,sK0) )
                      & v6_tops_1(X2,sK0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( ~ v4_tops_1(X2,sK0)
                      | ~ v3_pre_topc(X2,sK0) )
                    & v6_tops_1(X2,sK0) )
                  | ( ~ v6_tops_1(X3,X1)
                    & v4_tops_1(X3,X1)
                    & v3_pre_topc(X3,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( ~ v4_tops_1(X2,sK0)
                    | ~ v3_pre_topc(X2,sK0) )
                  & v6_tops_1(X2,sK0) )
                | ( ~ v6_tops_1(X3,sK1)
                  & v4_tops_1(X3,sK1)
                  & v3_pre_topc(X3,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( ~ v4_tops_1(X2,sK0)
                  | ~ v3_pre_topc(X2,sK0) )
                & v6_tops_1(X2,sK0) )
              | ( ~ v6_tops_1(X3,sK1)
                & v4_tops_1(X3,sK1)
                & v3_pre_topc(X3,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ( ( ~ v4_tops_1(sK2,sK0)
                | ~ v3_pre_topc(sK2,sK0) )
              & v6_tops_1(sK2,sK0) )
            | ( ~ v6_tops_1(X3,sK1)
              & v4_tops_1(X3,sK1)
              & v3_pre_topc(X3,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ( ( ( ~ v4_tops_1(sK2,sK0)
              | ~ v3_pre_topc(sK2,sK0) )
            & v6_tops_1(sK2,sK0) )
          | ( ~ v6_tops_1(X3,sK1)
            & v4_tops_1(X3,sK1)
            & v3_pre_topc(X3,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ( ( ~ v4_tops_1(sK2,sK0)
            | ~ v3_pre_topc(sK2,sK0) )
          & v6_tops_1(sK2,sK0) )
        | ( ~ v6_tops_1(sK3,sK1)
          & v4_tops_1(sK3,sK1)
          & v3_pre_topc(sK3,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ v4_tops_1(X2,X0)
                        | ~ v3_pre_topc(X2,X0) )
                      & v6_tops_1(X2,X0) )
                    | ( ~ v6_tops_1(X3,X1)
                      & v4_tops_1(X3,X1)
                      & v3_pre_topc(X3,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v6_tops_1(X2,X0)
                       => ( v4_tops_1(X2,X0)
                          & v3_pre_topc(X2,X0) ) )
                      & ( ( v4_tops_1(X3,X1)
                          & v3_pre_topc(X3,X1) )
                       => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v6_tops_1(X2,X0)
                     => ( v4_tops_1(X2,X0)
                        & v3_pre_topc(X2,X0) ) )
                    & ( ( v4_tops_1(X3,X1)
                        & v3_pre_topc(X3,X1) )
                     => v6_tops_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).

fof(f118,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f1651,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,sK2))
    | spl4_3
    | ~ spl4_6 ),
    inference(superposition,[],[f1619,f1607])).

fof(f1607,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f270,f1585])).

fof(f1585,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_6 ),
    inference(global_subsumption,[],[f649])).

fof(f649,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f648,f50])).

fof(f648,plain,
    ( sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f174,f109])).

fof(f109,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_6
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f174,plain,
    ( ~ v6_tops_1(sK2,sK0)
    | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f66,f52])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f270,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f214,f50])).

fof(f214,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f138,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f138,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f75,f52])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f1619,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1618,f50])).

fof(f1618,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1617,f52])).

fof(f1617,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1616,f94])).

fof(f94,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_3
  <=> v4_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1616,plain,
    ( ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f1611,f81])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1611,plain,
    ( ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2)))
    | v4_tops_1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_6 ),
    inference(superposition,[],[f70,f1585])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).

fof(f1577,plain,
    ( spl4_1
    | ~ spl4_4
    | ~ spl4_52 ),
    inference(avatar_contradiction_clause,[],[f1576])).

fof(f1576,plain,
    ( $false
    | spl4_1
    | ~ spl4_4
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f1575,f470])).

fof(f470,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f469,f181])).

fof(f181,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | spl4_1 ),
    inference(subsumption_resolution,[],[f180,f51])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f180,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f177,f86])).

fof(f86,plain,
    ( ~ v6_tops_1(sK3,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_1
  <=> v6_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f177,plain,
    ( sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | v6_tops_1(sK3,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f67,f53])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | v6_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f469,plain,
    ( sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3))
    | ~ r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_4 ),
    inference(resolution,[],[f185,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f185,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f184,f51])).

fof(f184,plain,
    ( r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f183,f99])).

fof(f99,plain,
    ( v4_tops_1(sK3,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_4
  <=> v4_tops_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f183,plain,
    ( ~ v4_tops_1(sK3,sK1)
    | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tops_1(X1,X0)
      | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1575,plain,
    ( r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1574,f1487])).

fof(f1487,plain,
    ( sK3 = k1_tops_1(sK1,sK3)
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f1485,f117])).

fof(f117,plain,(
    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1485,plain,
    ( k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3)
    | ~ spl4_52 ),
    inference(superposition,[],[f193,f578])).

fof(f578,plain,
    ( k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl4_52
  <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f193,plain,(
    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) ),
    inference(subsumption_resolution,[],[f191,f51])).

fof(f191,plain,
    ( k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f61,f53])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f1574,plain,(
    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f1573,f51])).

fof(f1573,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f1572,f53])).

fof(f1572,plain,
    ( r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f199,f139])).

fof(f139,plain,(
    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f137,f51])).

fof(f137,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f75,f53])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,k2_pre_topc(sK1,sK3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f121,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f121,plain,(
    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f119,f51])).

fof(f119,plain,
    ( r1_tarski(sK3,k2_pre_topc(sK1,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f60,f53])).

fof(f657,plain,
    ( spl4_2
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f654,f90])).

fof(f90,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f654,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_6 ),
    inference(superposition,[],[f267,f649])).

fof(f267,plain,(
    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f266,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f266,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f211,f50])).

fof(f211,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f138,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f627,plain,
    ( ~ spl4_5
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f626])).

fof(f626,plain,
    ( $false
    | ~ spl4_5
    | spl4_53 ),
    inference(subsumption_resolution,[],[f625,f51])).

fof(f625,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl4_5
    | spl4_53 ),
    inference(subsumption_resolution,[],[f624,f115])).

fof(f115,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f72,f53])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f624,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_5
    | spl4_53 ),
    inference(subsumption_resolution,[],[f623,f582])).

fof(f582,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | spl4_53 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl4_53
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f623,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f622,f104])).

fof(f104,plain,
    ( v3_pre_topc(sK3,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_5
  <=> v3_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f622,plain,
    ( ~ v3_pre_topc(sK3,sK1)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f65,f117])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f583,plain,
    ( spl4_52
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f574,f580,f576])).

fof(f574,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) ),
    inference(subsumption_resolution,[],[f558,f51])).

fof(f558,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)
    | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f115,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f112,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f54,f107,f102])).

fof(f54,plain,
    ( v6_tops_1(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f111,plain,
    ( spl4_4
    | spl4_6 ),
    inference(avatar_split_clause,[],[f55,f107,f97])).

fof(f55,plain,
    ( v6_tops_1(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f110,plain,
    ( ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f56,f107,f84])).

fof(f56,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,
    ( spl4_5
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f57,f92,f88,f102])).

fof(f57,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v3_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f100,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f58,f92,f88,f97])).

fof(f58,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | v4_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f95,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f59,f92,f88,f84])).

fof(f59,plain,
    ( ~ v4_tops_1(sK2,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v6_tops_1(sK3,sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (30876)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (30873)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.49  % (30867)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (30875)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (30882)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.50  % (30865)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (30866)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (30885)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (30872)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (30883)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (30868)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (30877)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (30886)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (30881)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (30869)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (30864)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (30888)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.32/0.53  % (30884)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.32/0.53  % (30880)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.32/0.53  % (30874)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.32/0.54  % (30863)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.32/0.54  % (30871)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.32/0.54  % (30873)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f1663,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f111,f112,f583,f627,f657,f1577,f1662])).
% 1.32/0.54  fof(f1662,plain,(
% 1.32/0.54    spl4_3 | ~spl4_6),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f1661])).
% 1.32/0.54  fof(f1661,plain,(
% 1.32/0.54    $false | (spl4_3 | ~spl4_6)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1651,f120])).
% 1.32/0.54  fof(f120,plain,(
% 1.32/0.54    r1_tarski(sK2,k2_pre_topc(sK0,sK2))),
% 1.32/0.54    inference(subsumption_resolution,[],[f118,f50])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    l1_pre_topc(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f42,plain,(
% 1.32/0.54    ((((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f41,f40,f39,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK1))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ? [X2] : (? [X3] : ((((~v4_tops_1(X2,sK0) | ~v3_pre_topc(X2,sK0)) & v6_tops_1(X2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f41,plain,(
% 1.32/0.54    ? [X3] : ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(X3,sK1) & v4_tops_1(X3,sK1) & v3_pre_topc(X3,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((((~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0)) & v6_tops_1(sK2,sK0)) | (~v6_tops_1(sK3,sK1) & v4_tops_1(sK3,sK1) & v3_pre_topc(sK3,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & v4_tops_1(X3,X1) & v3_pre_topc(X3,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f17])).
% 1.32/0.54  fof(f17,plain,(
% 1.32/0.54    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~v4_tops_1(X2,X0) | ~v3_pre_topc(X2,X0)) & v6_tops_1(X2,X0)) | (~v6_tops_1(X3,X1) & (v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f16])).
% 1.32/0.54  fof(f16,negated_conjecture,(
% 1.32/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 1.32/0.54    inference(negated_conjecture,[],[f15])).
% 1.32/0.54  fof(f15,conjecture,(
% 1.32/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v6_tops_1(X2,X0) => (v4_tops_1(X2,X0) & v3_pre_topc(X2,X0))) & ((v4_tops_1(X3,X1) & v3_pre_topc(X3,X1)) => v6_tops_1(X3,X1)))))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_tops_1)).
% 1.32/0.54  fof(f118,plain,(
% 1.32/0.54    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.32/0.54    inference(resolution,[],[f60,f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f19])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f5])).
% 1.32/0.54  fof(f5,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.32/0.54  fof(f1651,plain,(
% 1.32/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,sK2)) | (spl4_3 | ~spl4_6)),
% 1.32/0.54    inference(superposition,[],[f1619,f1607])).
% 1.32/0.54  fof(f1607,plain,(
% 1.32/0.54    sK2 = k1_tops_1(sK0,sK2) | ~spl4_6),
% 1.32/0.54    inference(superposition,[],[f270,f1585])).
% 1.32/0.54  fof(f1585,plain,(
% 1.32/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_6),
% 1.32/0.54    inference(global_subsumption,[],[f649])).
% 1.32/0.54  fof(f649,plain,(
% 1.32/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~spl4_6),
% 1.32/0.54    inference(subsumption_resolution,[],[f648,f50])).
% 1.32/0.54  fof(f648,plain,(
% 1.32/0.54    sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0) | ~spl4_6),
% 1.32/0.54    inference(subsumption_resolution,[],[f174,f109])).
% 1.32/0.54  fof(f109,plain,(
% 1.32/0.54    v6_tops_1(sK2,sK0) | ~spl4_6),
% 1.32/0.54    inference(avatar_component_clause,[],[f107])).
% 1.32/0.54  fof(f107,plain,(
% 1.32/0.54    spl4_6 <=> v6_tops_1(sK2,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.32/0.54  fof(f174,plain,(
% 1.32/0.54    ~v6_tops_1(sK2,sK0) | sK2 = k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.32/0.54    inference(resolution,[],[f66,f52])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f44])).
% 1.32/0.54  fof(f44,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 1.32/0.54  fof(f270,plain,(
% 1.32/0.54    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f214,f50])).
% 1.32/0.54  fof(f214,plain,(
% 1.32/0.54    k1_tops_1(sK0,k2_pre_topc(sK0,sK2)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK2))) | ~l1_pre_topc(sK0)),
% 1.32/0.54    inference(resolution,[],[f138,f77])).
% 1.32/0.54  fof(f77,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f36])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,axiom,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 1.32/0.54  fof(f138,plain,(
% 1.32/0.54    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f136,f50])).
% 1.32/0.54  fof(f136,plain,(
% 1.32/0.54    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.32/0.54    inference(resolution,[],[f75,f52])).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f32])).
% 1.32/0.54  fof(f32,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.32/0.54  fof(f1619,plain,(
% 1.32/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | (spl4_3 | ~spl4_6)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1618,f50])).
% 1.32/0.54  fof(f1618,plain,(
% 1.32/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~l1_pre_topc(sK0) | (spl4_3 | ~spl4_6)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1617,f52])).
% 1.32/0.54  fof(f1617,plain,(
% 1.32/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_3 | ~spl4_6)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1616,f94])).
% 1.32/0.54  fof(f94,plain,(
% 1.32/0.54    ~v4_tops_1(sK2,sK0) | spl4_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f92])).
% 1.32/0.54  fof(f92,plain,(
% 1.32/0.54    spl4_3 <=> v4_tops_1(sK2,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.54  fof(f1616,plain,(
% 1.32/0.54    ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_6),
% 1.32/0.54    inference(subsumption_resolution,[],[f1611,f81])).
% 1.32/0.54  fof(f81,plain,(
% 1.32/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.54    inference(equality_resolution,[],[f79])).
% 1.32/0.54  fof(f79,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(flattening,[],[f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.54    inference(nnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.54  fof(f1611,plain,(
% 1.32/0.54    ~r1_tarski(sK2,sK2) | ~r1_tarski(sK2,k2_pre_topc(sK0,k1_tops_1(sK0,sK2))) | v4_tops_1(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_6),
% 1.32/0.54    inference(superposition,[],[f70,f1585])).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f46])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f45])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f8])).
% 1.32/0.54  fof(f8,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_tops_1)).
% 1.32/0.54  fof(f1577,plain,(
% 1.32/0.54    spl4_1 | ~spl4_4 | ~spl4_52),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f1576])).
% 1.32/0.54  fof(f1576,plain,(
% 1.32/0.54    $false | (spl4_1 | ~spl4_4 | ~spl4_52)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1575,f470])).
% 1.32/0.54  fof(f470,plain,(
% 1.32/0.54    ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | (spl4_1 | ~spl4_4)),
% 1.32/0.54    inference(subsumption_resolution,[],[f469,f181])).
% 1.32/0.54  fof(f181,plain,(
% 1.32/0.54    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | spl4_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f180,f51])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    l1_pre_topc(sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f180,plain,(
% 1.32/0.54    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1) | spl4_1),
% 1.32/0.54    inference(subsumption_resolution,[],[f177,f86])).
% 1.32/0.54  fof(f86,plain,(
% 1.32/0.54    ~v6_tops_1(sK3,sK1) | spl4_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f84])).
% 1.32/0.54  fof(f84,plain,(
% 1.32/0.54    spl4_1 <=> v6_tops_1(sK3,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.54  fof(f177,plain,(
% 1.32/0.54    sK3 != k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | v6_tops_1(sK3,sK1) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f67,f53])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | v6_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f44])).
% 1.32/0.54  fof(f469,plain,(
% 1.32/0.54    sK3 = k1_tops_1(sK1,k2_pre_topc(sK1,sK3)) | ~r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~spl4_4),
% 1.32/0.54    inference(resolution,[],[f185,f80])).
% 1.32/0.54  fof(f80,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f48])).
% 1.32/0.54  fof(f185,plain,(
% 1.32/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~spl4_4),
% 1.32/0.54    inference(subsumption_resolution,[],[f184,f51])).
% 1.32/0.54  fof(f184,plain,(
% 1.32/0.54    r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1) | ~spl4_4),
% 1.32/0.54    inference(subsumption_resolution,[],[f183,f99])).
% 1.32/0.54  fof(f99,plain,(
% 1.32/0.54    v4_tops_1(sK3,sK1) | ~spl4_4),
% 1.32/0.54    inference(avatar_component_clause,[],[f97])).
% 1.32/0.54  fof(f97,plain,(
% 1.32/0.54    spl4_4 <=> v4_tops_1(sK3,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.32/0.54  fof(f183,plain,(
% 1.32/0.54    ~v4_tops_1(sK3,sK1) | r1_tarski(k1_tops_1(sK1,k2_pre_topc(sK1,sK3)),sK3) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f68,f53])).
% 1.32/0.54  fof(f68,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_tops_1(X1,X0) | r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f46])).
% 1.32/0.54  fof(f1575,plain,(
% 1.32/0.54    r1_tarski(sK3,k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~spl4_52),
% 1.32/0.54    inference(forward_demodulation,[],[f1574,f1487])).
% 1.32/0.54  fof(f1487,plain,(
% 1.32/0.54    sK3 = k1_tops_1(sK1,sK3) | ~spl4_52),
% 1.32/0.54    inference(forward_demodulation,[],[f1485,f117])).
% 1.32/0.54  fof(f117,plain,(
% 1.32/0.54    sK3 = k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.32/0.54    inference(resolution,[],[f73,f53])).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.32/0.54  fof(f1485,plain,(
% 1.32/0.54    k3_subset_1(u1_struct_0(sK1),k3_subset_1(u1_struct_0(sK1),sK3)) = k1_tops_1(sK1,sK3) | ~spl4_52),
% 1.32/0.54    inference(superposition,[],[f193,f578])).
% 1.32/0.54  fof(f578,plain,(
% 1.32/0.54    k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~spl4_52),
% 1.32/0.54    inference(avatar_component_clause,[],[f576])).
% 1.32/0.54  fof(f576,plain,(
% 1.32/0.54    spl4_52 <=> k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.32/0.54  fof(f193,plain,(
% 1.32/0.54    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f191,f51])).
% 1.32/0.54  fof(f191,plain,(
% 1.32/0.54    k1_tops_1(sK1,sK3) = k3_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f61,f53])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f7])).
% 1.32/0.54  fof(f7,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 1.32/0.54  fof(f1574,plain,(
% 1.32/0.54    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f1573,f51])).
% 1.32/0.54  fof(f1573,plain,(
% 1.32/0.54    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(subsumption_resolution,[],[f1572,f53])).
% 1.32/0.54  fof(f1572,plain,(
% 1.32/0.54    r1_tarski(k1_tops_1(sK1,sK3),k1_tops_1(sK1,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f199,f139])).
% 1.32/0.54  fof(f139,plain,(
% 1.32/0.54    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.32/0.54    inference(subsumption_resolution,[],[f137,f51])).
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f75,f53])).
% 1.32/0.54  fof(f199,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(k2_pre_topc(sK1,sK3),k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,sK3),k1_tops_1(X0,k2_pre_topc(sK1,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(resolution,[],[f121,f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.32/0.54  fof(f121,plain,(
% 1.32/0.54    r1_tarski(sK3,k2_pre_topc(sK1,sK3))),
% 1.32/0.54    inference(subsumption_resolution,[],[f119,f51])).
% 1.32/0.54  fof(f119,plain,(
% 1.32/0.54    r1_tarski(sK3,k2_pre_topc(sK1,sK3)) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f60,f53])).
% 1.32/0.54  fof(f657,plain,(
% 1.32/0.54    spl4_2 | ~spl4_6),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f656])).
% 1.32/0.54  fof(f656,plain,(
% 1.32/0.54    $false | (spl4_2 | ~spl4_6)),
% 1.32/0.54    inference(subsumption_resolution,[],[f654,f90])).
% 1.32/0.54  fof(f90,plain,(
% 1.32/0.54    ~v3_pre_topc(sK2,sK0) | spl4_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f88])).
% 1.32/0.54  fof(f88,plain,(
% 1.32/0.54    spl4_2 <=> v3_pre_topc(sK2,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.54  fof(f654,plain,(
% 1.32/0.54    v3_pre_topc(sK2,sK0) | ~spl4_6),
% 1.32/0.54    inference(superposition,[],[f267,f649])).
% 1.32/0.54  fof(f267,plain,(
% 1.32/0.54    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0)),
% 1.32/0.54    inference(subsumption_resolution,[],[f266,f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    v2_pre_topc(sK0)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f266,plain,(
% 1.32/0.54    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~v2_pre_topc(sK0)),
% 1.32/0.54    inference(subsumption_resolution,[],[f211,f50])).
% 1.32/0.54  fof(f211,plain,(
% 1.32/0.54    v3_pre_topc(k1_tops_1(sK0,k2_pre_topc(sK0,sK2)),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 1.32/0.54    inference(resolution,[],[f138,f74])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f31])).
% 1.32/0.54  fof(f31,plain,(
% 1.32/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f11])).
% 1.32/0.54  fof(f11,axiom,(
% 1.32/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.32/0.54  fof(f627,plain,(
% 1.32/0.54    ~spl4_5 | spl4_53),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f626])).
% 1.32/0.54  fof(f626,plain,(
% 1.32/0.54    $false | (~spl4_5 | spl4_53)),
% 1.32/0.54    inference(subsumption_resolution,[],[f625,f51])).
% 1.32/0.54  fof(f625,plain,(
% 1.32/0.54    ~l1_pre_topc(sK1) | (~spl4_5 | spl4_53)),
% 1.32/0.54    inference(subsumption_resolution,[],[f624,f115])).
% 1.32/0.54  fof(f115,plain,(
% 1.32/0.54    m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.32/0.54    inference(resolution,[],[f72,f53])).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f28])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.32/0.54  fof(f624,plain,(
% 1.32/0.54    ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | (~spl4_5 | spl4_53)),
% 1.32/0.54    inference(subsumption_resolution,[],[f623,f582])).
% 1.32/0.54  fof(f582,plain,(
% 1.32/0.54    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | spl4_53),
% 1.32/0.54    inference(avatar_component_clause,[],[f580])).
% 1.32/0.54  fof(f580,plain,(
% 1.32/0.54    spl4_53 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 1.32/0.54  fof(f623,plain,(
% 1.32/0.54    v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~spl4_5),
% 1.32/0.54    inference(subsumption_resolution,[],[f622,f104])).
% 1.32/0.54  fof(f104,plain,(
% 1.32/0.54    v3_pre_topc(sK3,sK1) | ~spl4_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f102])).
% 1.32/0.54  fof(f102,plain,(
% 1.32/0.54    spl4_5 <=> v3_pre_topc(sK3,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.32/0.54  fof(f622,plain,(
% 1.32/0.54    ~v3_pre_topc(sK3,sK1) | v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK1),sK3),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(superposition,[],[f65,f117])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f43])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(nnf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 1.32/0.54  fof(f583,plain,(
% 1.32/0.54    spl4_52 | ~spl4_53),
% 1.32/0.54    inference(avatar_split_clause,[],[f574,f580,f576])).
% 1.32/0.54  fof(f574,plain,(
% 1.32/0.54    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3))),
% 1.32/0.54    inference(subsumption_resolution,[],[f558,f51])).
% 1.32/0.54  fof(f558,plain,(
% 1.32/0.54    ~v4_pre_topc(k3_subset_1(u1_struct_0(sK1),sK3),sK1) | k3_subset_1(u1_struct_0(sK1),sK3) = k2_pre_topc(sK1,k3_subset_1(u1_struct_0(sK1),sK3)) | ~l1_pre_topc(sK1)),
% 1.32/0.54    inference(resolution,[],[f115,f62])).
% 1.32/0.54  fof(f62,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f22])).
% 1.32/0.54  fof(f22,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(flattening,[],[f21])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f6])).
% 1.32/0.54  fof(f6,axiom,(
% 1.32/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.32/0.54  fof(f112,plain,(
% 1.32/0.54    spl4_5 | spl4_6),
% 1.32/0.54    inference(avatar_split_clause,[],[f54,f107,f102])).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    v6_tops_1(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f111,plain,(
% 1.32/0.54    spl4_4 | spl4_6),
% 1.32/0.54    inference(avatar_split_clause,[],[f55,f107,f97])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    v6_tops_1(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f110,plain,(
% 1.32/0.54    ~spl4_1 | spl4_6),
% 1.32/0.54    inference(avatar_split_clause,[],[f56,f107,f84])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    v6_tops_1(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f105,plain,(
% 1.32/0.54    spl4_5 | ~spl4_2 | ~spl4_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f57,f92,f88,f102])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v3_pre_topc(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f100,plain,(
% 1.32/0.54    spl4_4 | ~spl4_2 | ~spl4_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f58,f92,f88,f97])).
% 1.32/0.54  fof(f58,plain,(
% 1.32/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | v4_tops_1(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  fof(f95,plain,(
% 1.32/0.54    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 1.32/0.54    inference(avatar_split_clause,[],[f59,f92,f88,f84])).
% 1.32/0.54  fof(f59,plain,(
% 1.32/0.54    ~v4_tops_1(sK2,sK0) | ~v3_pre_topc(sK2,sK0) | ~v6_tops_1(sK3,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f42])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (30873)------------------------------
% 1.32/0.54  % (30873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (30873)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (30873)Memory used [KB]: 11513
% 1.41/0.54  % (30873)Time elapsed: 0.122 s
% 1.41/0.54  % (30873)------------------------------
% 1.41/0.54  % (30873)------------------------------
% 1.41/0.55  % (30858)Success in time 0.189 s
%------------------------------------------------------------------------------
