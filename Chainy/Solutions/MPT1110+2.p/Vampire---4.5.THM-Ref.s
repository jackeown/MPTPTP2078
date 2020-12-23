%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1110+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 2.88s
% Output     : Refutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 133 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  179 ( 491 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5760,plain,(
    $false ),
    inference(global_subsumption,[],[f3886,f5726])).

fof(f5726,plain,(
    ~ r1_tarski(u1_struct_0(sK57),u1_struct_0(sK56)) ),
    inference(unit_resulting_resolution,[],[f3443,f3863,f2686])).

fof(f2686,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1857])).

fof(f1857,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1856])).

fof(f1856,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f3863,plain,(
    ~ r1_tarski(sK58,u1_struct_0(sK56)) ),
    inference(unit_resulting_resolution,[],[f2636,f2642])).

fof(f2642,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2353])).

fof(f2353,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2636,plain,(
    ~ m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK56))) ),
    inference(cnf_transformation,[],[f2352])).

fof(f2352,plain,
    ( ~ m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK56)))
    & m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK57)))
    & m1_pre_topc(sK57,sK56)
    & l1_pre_topc(sK56) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK56,sK57,sK58])],[f1821,f2351,f2350,f2349])).

fof(f2349,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK56)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,sK56) )
      & l1_pre_topc(sK56) ) ),
    introduced(choice_axiom,[])).

fof(f2350,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK56)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_pre_topc(X1,sK56) )
   => ( ? [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK56)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK57))) )
      & m1_pre_topc(sK57,sK56) ) ),
    introduced(choice_axiom,[])).

fof(f2351,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK56)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK57))) )
   => ( ~ m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK56)))
      & m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK57))) ) ),
    introduced(choice_axiom,[])).

fof(f1821,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1814])).

fof(f1814,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f1813])).

fof(f1813,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f3443,plain,(
    r1_tarski(sK58,u1_struct_0(sK57)) ),
    inference(unit_resulting_resolution,[],[f2635,f2641])).

fof(f2641,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2353])).

fof(f2635,plain,(
    m1_subset_1(sK58,k1_zfmisc_1(u1_struct_0(sK57))) ),
    inference(cnf_transformation,[],[f2352])).

fof(f3886,plain,(
    r1_tarski(u1_struct_0(sK57),u1_struct_0(sK56)) ),
    inference(forward_demodulation,[],[f3885,f3406])).

fof(f3406,plain,(
    u1_struct_0(sK57) = k2_struct_0(sK57) ),
    inference(unit_resulting_resolution,[],[f3368,f2864])).

fof(f2864,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1955])).

fof(f1955,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1770])).

fof(f1770,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f3368,plain,(
    l1_struct_0(sK57) ),
    inference(unit_resulting_resolution,[],[f3335,f2680])).

fof(f2680,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1850])).

fof(f1850,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1776])).

fof(f1776,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3335,plain,(
    l1_pre_topc(sK57) ),
    inference(unit_resulting_resolution,[],[f2633,f2634,f2678])).

fof(f2678,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f1849])).

fof(f1849,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1778])).

fof(f1778,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2634,plain,(
    m1_pre_topc(sK57,sK56) ),
    inference(cnf_transformation,[],[f2352])).

fof(f2633,plain,(
    l1_pre_topc(sK56) ),
    inference(cnf_transformation,[],[f2352])).

fof(f3885,plain,(
    r1_tarski(k2_struct_0(sK57),u1_struct_0(sK56)) ),
    inference(forward_demodulation,[],[f3877,f3345])).

fof(f3345,plain,(
    u1_struct_0(sK56) = k2_struct_0(sK56) ),
    inference(unit_resulting_resolution,[],[f3308,f2864])).

fof(f3308,plain,(
    l1_struct_0(sK56) ),
    inference(unit_resulting_resolution,[],[f2633,f2680])).

fof(f3877,plain,(
    r1_tarski(k2_struct_0(sK57),k2_struct_0(sK56)) ),
    inference(unit_resulting_resolution,[],[f3612,f2845])).

fof(f2845,plain,(
    ! [X0,X1] :
      ( ~ sP17(X0,X1)
      | r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f2469])).

fof(f2469,plain,(
    ! [X0,X1] :
      ( ( sP17(X0,X1)
        | ( ~ sP16(X1,X0,sK94(X0,X1))
          & m1_subset_1(sK94(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP16(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP17(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK94])],[f2467,f2468])).

fof(f2468,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP16(X1,X0,X2)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ sP16(X1,X0,sK94(X0,X1))
        & m1_subset_1(sK94(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2467,plain,(
    ! [X0,X1] :
      ( ( sP17(X0,X1)
        | ? [X2] :
            ( ~ sP16(X1,X0,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
      & ( ( ! [X3] :
              ( sP16(X1,X0,X3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(k2_struct_0(X0),k2_struct_0(X1)) )
        | ~ sP17(X0,X1) ) ) ),
    inference(rectify,[],[f2466])).

fof(f2466,plain,(
    ! [X1,X0] :
      ( ( sP17(X1,X0)
        | ? [X2] :
            ( ~ sP16(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP16(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP17(X1,X0) ) ) ),
    inference(flattening,[],[f2465])).

fof(f2465,plain,(
    ! [X1,X0] :
      ( ( sP17(X1,X0)
        | ? [X2] :
            ( ~ sP16(X0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
      & ( ( ! [X2] :
              ( sP16(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
        | ~ sP17(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X1,X0] :
      ( sP17(X1,X0)
    <=> ( ! [X2] :
            ( sP16(X0,X1,X2)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP17])])).

fof(f3612,plain,(
    sP17(sK57,sK56) ),
    inference(unit_resulting_resolution,[],[f2634,f3386,f2843])).

fof(f2843,plain,(
    ! [X0,X1] :
      ( ~ sP18(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | sP17(X1,X0) ) ),
    inference(cnf_transformation,[],[f2464])).

fof(f2464,plain,(
    ! [X0,X1] :
      ( ( ( m1_pre_topc(X1,X0)
          | ~ sP17(X1,X0) )
        & ( sP17(X1,X0)
          | ~ m1_pre_topc(X1,X0) ) )
      | ~ sP18(X0,X1) ) ),
    inference(nnf_transformation,[],[f2283])).

fof(f2283,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
      <=> sP17(X1,X0) )
      | ~ sP18(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP18])])).

fof(f3386,plain,(
    sP18(sK56,sK57) ),
    inference(unit_resulting_resolution,[],[f2633,f3335,f2857])).

fof(f2857,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | sP18(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2284])).

fof(f2284,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP18(X0,X1)
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f1948,f2283,f2282,f2281,f2280])).

fof(f2280,plain,(
    ! [X2,X1,X0] :
      ( sP15(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & r2_hidden(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP15])])).

fof(f2281,plain,(
    ! [X0,X1,X2] :
      ( sP16(X0,X1,X2)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> sP15(X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP16])])).

fof(f1948,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1771])).

fof(f1771,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
%------------------------------------------------------------------------------
