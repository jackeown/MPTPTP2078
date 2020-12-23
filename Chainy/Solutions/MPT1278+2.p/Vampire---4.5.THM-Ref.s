%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1278+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 1.61s
% Output     : Refutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 120 expanded)
%              Number of leaves         :    9 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  220 ( 682 expanded)
%              Number of equality atoms :   31 ( 113 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5956,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5955,f5552])).

fof(f5552,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4132])).

fof(f4132,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3385])).

fof(f3385,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3384])).

fof(f3384,plain,(
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

fof(f5955,plain,(
    ~ r1_tarski(sK149,sK149) ),
    inference(resolution,[],[f5730,f5770])).

fof(f5770,plain,(
    sP30(sK148,sK149) ),
    inference(subsumption_resolution,[],[f5768,f5697])).

fof(f5697,plain,(
    v2_tops_1(sK149,sK148) ),
    inference(subsumption_resolution,[],[f5696,f3958])).

fof(f3958,plain,(
    v2_pre_topc(sK148) ),
    inference(cnf_transformation,[],[f3289])).

fof(f3289,plain,
    ( k1_xboole_0 != sK149
    & v3_tops_1(sK149,sK148)
    & v3_pre_topc(sK149,sK148)
    & m1_subset_1(sK149,k1_zfmisc_1(u1_struct_0(sK148)))
    & l1_pre_topc(sK148)
    & v2_pre_topc(sK148) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK148,sK149])],[f2199,f3288,f3287])).

fof(f3287,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 != X1
            & v3_tops_1(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,sK148)
          & v3_pre_topc(X1,sK148)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK148))) )
      & l1_pre_topc(sK148)
      & v2_pre_topc(sK148) ) ),
    introduced(choice_axiom,[])).

fof(f3288,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & v3_tops_1(X1,sK148)
        & v3_pre_topc(X1,sK148)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK148))) )
   => ( k1_xboole_0 != sK149
      & v3_tops_1(sK149,sK148)
      & v3_pre_topc(sK149,sK148)
      & m1_subset_1(sK149,k1_zfmisc_1(u1_struct_0(sK148))) ) ),
    introduced(choice_axiom,[])).

fof(f2199,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2198])).

fof(f2198,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2188])).

fof(f2188,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2187])).

fof(f2187,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_tops_1)).

fof(f5696,plain,
    ( v2_tops_1(sK149,sK148)
    | ~ v2_pre_topc(sK148) ),
    inference(subsumption_resolution,[],[f5695,f3959])).

fof(f3959,plain,(
    l1_pre_topc(sK148) ),
    inference(cnf_transformation,[],[f3289])).

fof(f5695,plain,
    ( v2_tops_1(sK149,sK148)
    | ~ l1_pre_topc(sK148)
    | ~ v2_pre_topc(sK148) ),
    inference(subsumption_resolution,[],[f5632,f3962])).

fof(f3962,plain,(
    v3_tops_1(sK149,sK148) ),
    inference(cnf_transformation,[],[f3289])).

fof(f5632,plain,
    ( ~ v3_tops_1(sK149,sK148)
    | v2_tops_1(sK149,sK148)
    | ~ l1_pre_topc(sK148)
    | ~ v2_pre_topc(sK148) ),
    inference(resolution,[],[f3960,f3995])).

fof(f3995,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2230])).

fof(f2230,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2229])).

fof(f2229,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2089])).

fof(f2089,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tops_1)).

fof(f3960,plain,(
    m1_subset_1(sK149,k1_zfmisc_1(u1_struct_0(sK148))) ),
    inference(cnf_transformation,[],[f3289])).

fof(f5768,plain,
    ( ~ v2_tops_1(sK149,sK148)
    | sP30(sK148,sK149) ),
    inference(resolution,[],[f5732,f4286])).

fof(f4286,plain,(
    ! [X0,X1] :
      ( ~ sP31(X0,X1)
      | ~ v2_tops_1(X0,X1)
      | sP30(X1,X0) ) ),
    inference(cnf_transformation,[],[f3448])).

fof(f3448,plain,(
    ! [X0,X1] :
      ( ( ( v2_tops_1(X0,X1)
          | ~ sP30(X1,X0) )
        & ( sP30(X1,X0)
          | ~ v2_tops_1(X0,X1) ) )
      | ~ sP31(X0,X1) ) ),
    inference(rectify,[],[f3447])).

fof(f3447,plain,(
    ! [X1,X0] :
      ( ( ( v2_tops_1(X1,X0)
          | ~ sP30(X0,X1) )
        & ( sP30(X0,X1)
          | ~ v2_tops_1(X1,X0) ) )
      | ~ sP31(X1,X0) ) ),
    inference(nnf_transformation,[],[f3102])).

fof(f3102,plain,(
    ! [X1,X0] :
      ( ( v2_tops_1(X1,X0)
      <=> sP30(X0,X1) )
      | ~ sP31(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP31])])).

fof(f5732,plain,(
    sP31(sK149,sK148) ),
    inference(subsumption_resolution,[],[f5731,f3958])).

fof(f5731,plain,
    ( sP31(sK149,sK148)
    | ~ v2_pre_topc(sK148) ),
    inference(subsumption_resolution,[],[f5659,f3959])).

fof(f5659,plain,
    ( sP31(sK149,sK148)
    | ~ l1_pre_topc(sK148)
    | ~ v2_pre_topc(sK148) ),
    inference(resolution,[],[f3960,f4293])).

fof(f4293,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP31(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3103])).

fof(f3103,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP31(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f2452,f3102,f3101])).

fof(f3101,plain,(
    ! [X0,X1] :
      ( sP30(X0,X1)
    <=> ! [X2] :
          ( k1_xboole_0 = X2
          | ~ v3_pre_topc(X2,X0)
          | ~ r1_tarski(X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP30])])).

fof(f2452,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2451])).

fof(f2451,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2177])).

fof(f2177,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f5730,plain,(
    ! [X22] :
      ( ~ sP30(sK148,X22)
      | ~ r1_tarski(sK149,X22) ) ),
    inference(subsumption_resolution,[],[f5729,f3963])).

fof(f3963,plain,(
    k1_xboole_0 != sK149 ),
    inference(cnf_transformation,[],[f3289])).

fof(f5729,plain,(
    ! [X22] :
      ( ~ r1_tarski(sK149,X22)
      | k1_xboole_0 = sK149
      | ~ sP30(sK148,X22) ) ),
    inference(subsumption_resolution,[],[f5658,f3961])).

fof(f3961,plain,(
    v3_pre_topc(sK149,sK148) ),
    inference(cnf_transformation,[],[f3289])).

fof(f5658,plain,(
    ! [X22] :
      ( ~ v3_pre_topc(sK149,sK148)
      | ~ r1_tarski(sK149,X22)
      | k1_xboole_0 = sK149
      | ~ sP30(sK148,X22) ) ),
    inference(resolution,[],[f3960,f4288])).

fof(f4288,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X1)
      | k1_xboole_0 = X3
      | ~ sP30(X0,X1) ) ),
    inference(cnf_transformation,[],[f3452])).

fof(f3452,plain,(
    ! [X0,X1] :
      ( ( sP30(X0,X1)
        | ( k1_xboole_0 != sK188(X0,X1)
          & v3_pre_topc(sK188(X0,X1),X0)
          & r1_tarski(sK188(X0,X1),X1)
          & m1_subset_1(sK188(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP30(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK188])],[f3450,f3451])).

fof(f3451,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_xboole_0 != X2
          & v3_pre_topc(X2,X0)
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 != sK188(X0,X1)
        & v3_pre_topc(sK188(X0,X1),X0)
        & r1_tarski(sK188(X0,X1),X1)
        & m1_subset_1(sK188(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3450,plain,(
    ! [X0,X1] :
      ( ( sP30(X0,X1)
        | ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,X0)
            | ~ r1_tarski(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP30(X0,X1) ) ) ),
    inference(rectify,[],[f3449])).

fof(f3449,plain,(
    ! [X0,X1] :
      ( ( sP30(X0,X1)
        | ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,X0)
            & r1_tarski(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ v3_pre_topc(X2,X0)
            | ~ r1_tarski(X2,X1)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP30(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3101])).
%------------------------------------------------------------------------------
