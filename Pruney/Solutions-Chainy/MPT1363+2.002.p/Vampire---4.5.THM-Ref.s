%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:44 EST 2020

% Result     : Theorem 1.83s
% Output     : Refutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 991 expanded)
%              Number of leaves         :   24 ( 350 expanded)
%              Depth                    :   27
%              Number of atoms          :  524 (6810 expanded)
%              Number of equality atoms :   72 ( 193 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1625,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1624,f166])).

fof(f166,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
    inference(resolution,[],[f86,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f86,plain,(
    r1_tarski(sK8,sK7) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,
    ( ~ v2_compts_1(sK8,sK6)
    & v4_pre_topc(sK8,sK6)
    & r1_tarski(sK8,sK7)
    & v2_compts_1(sK7,sK6)
    & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6)
    & v2_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f59,f58,f57])).

fof(f57,plain,
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
              ( ~ v2_compts_1(X2,sK6)
              & v4_pre_topc(X2,sK6)
              & r1_tarski(X2,X1)
              & v2_compts_1(X1,sK6)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6)
      & v2_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_compts_1(X2,sK6)
            & v4_pre_topc(X2,sK6)
            & r1_tarski(X2,X1)
            & v2_compts_1(X1,sK6)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ? [X2] :
          ( ~ v2_compts_1(X2,sK6)
          & v4_pre_topc(X2,sK6)
          & r1_tarski(X2,sK7)
          & v2_compts_1(sK7,sK6)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X2] :
        ( ~ v2_compts_1(X2,sK6)
        & v4_pre_topc(X2,sK6)
        & r1_tarski(X2,sK7)
        & v2_compts_1(sK7,sK6)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) )
   => ( ~ v2_compts_1(sK8,sK6)
      & v4_pre_topc(sK8,sK6)
      & r1_tarski(sK8,sK7)
      & v2_compts_1(sK7,sK6)
      & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(f1624,plain,(
    ~ m1_subset_1(sK8,k1_zfmisc_1(sK7)) ),
    inference(forward_demodulation,[],[f1623,f203])).

fof(f203,plain,(
    sK7 = u1_struct_0(k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f188,f82])).

fof(f82,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f188,plain,
    ( sK7 = u1_struct_0(k1_pre_topc(sK6,sK7))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f83,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f83,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f60])).

fof(f1623,plain,(
    ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))) ),
    inference(subsumption_resolution,[],[f1621,f207])).

fof(f207,plain,(
    m1_pre_topc(k1_pre_topc(sK6,sK7),sK6) ),
    inference(subsumption_resolution,[],[f193,f82])).

fof(f193,plain,
    ( m1_pre_topc(k1_pre_topc(sK6,sK7),sK6)
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f83,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f1621,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ m1_pre_topc(k1_pre_topc(sK6,sK7),sK6) ),
    inference(resolution,[],[f1619,f151])).

fof(f151,plain,(
    ! [X6,X5] :
      ( sP3(sK6,X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_pre_topc(X5,sK6) ) ),
    inference(resolution,[],[f82,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP3(X0,X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f33,f52,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
          & v4_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( v4_pre_topc(X2,X1)
      <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f1619,plain,(
    ~ sP3(sK6,k1_pre_topc(sK6,sK7),sK8) ),
    inference(subsumption_resolution,[],[f591,f1122])).

fof(f1122,plain,(
    ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f1118,f1056])).

fof(f1056,plain,(
    v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f1055,f141])).

fof(f141,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
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

fof(f1055,plain,
    ( v2_compts_1(sK7,k1_pre_topc(sK6,sK7))
    | ~ r1_tarski(sK7,sK7) ),
    inference(resolution,[],[f819,f130])).

fof(f819,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(sK7))
    | v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) ),
    inference(forward_demodulation,[],[f817,f203])).

fof(f817,plain,
    ( v2_compts_1(sK7,k1_pre_topc(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))) ),
    inference(resolution,[],[f816,f133])).

fof(f133,plain,(
    ! [X0,X3] :
      ( v2_compts_1(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X3) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( v2_compts_1(X3,X0)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ~ v2_compts_1(sK9(X0,X1),X0)
          & sK9(X0,X1) = X1
          & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v2_compts_1(X2,X0)
          & X1 = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v2_compts_1(sK9(X0,X1),X0)
        & sK9(X0,X1) = X1
        & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ~ v2_compts_1(X2,X0)
            & X1 = X2
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X0)
            | X1 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X2] :
      ( ( sP0(X1,X2)
        | ? [X3] :
            ( ~ v2_compts_1(X3,X1)
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v2_compts_1(X3,X1)
            | X2 != X3
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X1,X2) ) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X1,X2] :
      ( sP0(X1,X2)
    <=> ! [X3] :
          ( v2_compts_1(X3,X1)
          | X2 != X3
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f816,plain,(
    sP0(k1_pre_topc(sK6,sK7),sK7) ),
    inference(subsumption_resolution,[],[f814,f85])).

fof(f85,plain,(
    v2_compts_1(sK7,sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f814,plain,
    ( sP0(k1_pre_topc(sK6,sK7),sK7)
    | ~ v2_compts_1(sK7,sK6) ),
    inference(resolution,[],[f811,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_compts_1(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( ( v2_compts_1(X0,X2)
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | ~ v2_compts_1(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ( ( v2_compts_1(X2,X0)
          | ~ sP0(X1,X2) )
        & ( sP0(X1,X2)
          | ~ v2_compts_1(X2,X0) ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ( v2_compts_1(X2,X0)
      <=> sP0(X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f811,plain,(
    sP1(sK7,k1_pre_topc(sK6,sK7),sK6) ),
    inference(subsumption_resolution,[],[f810,f141])).

fof(f810,plain,
    ( ~ r1_tarski(sK7,sK7)
    | sP1(sK7,k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f806,f306])).

fof(f306,plain,(
    sK7 = k2_struct_0(k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f305,f82])).

fof(f305,plain,
    ( sK7 = k2_struct_0(k1_pre_topc(sK6,sK7))
    | ~ l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f304,f83])).

fof(f304,plain,
    ( sK7 = k2_struct_0(k1_pre_topc(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(subsumption_resolution,[],[f297,f206])).

fof(f206,plain,(
    v1_pre_topc(k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f192,f82])).

fof(f192,plain,
    ( v1_pre_topc(k1_pre_topc(sK6,sK7))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f83,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f297,plain,
    ( sK7 = k2_struct_0(k1_pre_topc(sK6,sK7))
    | ~ v1_pre_topc(k1_pre_topc(sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(resolution,[],[f207,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
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
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f806,plain,
    ( ~ r1_tarski(sK7,k2_struct_0(k1_pre_topc(sK6,sK7)))
    | sP1(sK7,k1_pre_topc(sK6,sK7),sK6) ),
    inference(resolution,[],[f202,f207])).

fof(f202,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK6)
      | ~ r1_tarski(sK7,k2_struct_0(X1))
      | sP1(sK7,X1,sK6) ) ),
    inference(subsumption_resolution,[],[f186,f82])).

fof(f186,plain,(
    ! [X1] :
      ( sP1(sK7,X1,sK6)
      | ~ r1_tarski(sK7,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK6)
      | ~ l1_pre_topc(sK6) ) ),
    inference(resolution,[],[f83,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X2,X1,X0)
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f32,f49,f48])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f1118,plain,
    ( ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))
    | ~ v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) ),
    inference(resolution,[],[f895,f465])).

fof(f465,plain,
    ( v1_compts_1(k1_pre_topc(sK6,sK7))
    | ~ v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f458,f298])).

fof(f298,plain,(
    l1_pre_topc(k1_pre_topc(sK6,sK7)) ),
    inference(resolution,[],[f207,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK6)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f82,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f458,plain,
    ( ~ v2_compts_1(sK7,k1_pre_topc(sK6,sK7))
    | v1_compts_1(k1_pre_topc(sK6,sK7))
    | ~ l1_pre_topc(k1_pre_topc(sK6,sK7)) ),
    inference(superposition,[],[f94,f306])).

fof(f94,plain,(
    ! [X0] :
      ( v1_compts_1(X0)
      | ~ v2_compts_1(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f895,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK6,sK7))
    | ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f894,f166])).

fof(f894,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(sK7))
    | ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))
    | ~ v1_compts_1(k1_pre_topc(sK6,sK7)) ),
    inference(forward_demodulation,[],[f893,f203])).

fof(f893,plain,
    ( ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))
    | ~ v1_compts_1(k1_pre_topc(sK6,sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))) ),
    inference(subsumption_resolution,[],[f889,f298])).

fof(f889,plain,
    ( ~ v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))
    | ~ v1_compts_1(k1_pre_topc(sK6,sK7))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))
    | ~ l1_pre_topc(k1_pre_topc(sK6,sK7)) ),
    inference(resolution,[],[f888,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( v2_compts_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ v1_compts_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_compts_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v1_compts_1(X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v1_compts_1(X0) )
           => v2_compts_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(f888,plain,(
    ~ v2_compts_1(sK8,k1_pre_topc(sK6,sK7)) ),
    inference(subsumption_resolution,[],[f885,f865])).

fof(f865,plain,(
    ~ sP0(k1_pre_topc(sK6,sK7),sK8) ),
    inference(subsumption_resolution,[],[f864,f88])).

fof(f88,plain,(
    ~ v2_compts_1(sK8,sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f864,plain,
    ( v2_compts_1(sK8,sK6)
    | ~ sP0(k1_pre_topc(sK6,sK7),sK8) ),
    inference(resolution,[],[f857,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v2_compts_1(X0,X2)
      | ~ sP0(X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f857,plain,(
    sP1(sK8,k1_pre_topc(sK6,sK7),sK6) ),
    inference(subsumption_resolution,[],[f856,f86])).

fof(f856,plain,
    ( ~ r1_tarski(sK8,sK7)
    | sP1(sK8,k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f852,f306])).

fof(f852,plain,
    ( ~ r1_tarski(sK8,k2_struct_0(k1_pre_topc(sK6,sK7)))
    | sP1(sK8,k1_pre_topc(sK6,sK7),sK6) ),
    inference(resolution,[],[f234,f207])).

fof(f234,plain,(
    ! [X1] :
      ( ~ m1_pre_topc(X1,sK6)
      | ~ r1_tarski(sK8,k2_struct_0(X1))
      | sP1(sK8,X1,sK6) ) ),
    inference(subsumption_resolution,[],[f218,f82])).

fof(f218,plain,(
    ! [X1] :
      ( sP1(sK8,X1,sK6)
      | ~ r1_tarski(sK8,k2_struct_0(X1))
      | ~ m1_pre_topc(X1,sK6)
      | ~ l1_pre_topc(sK6) ) ),
    inference(resolution,[],[f84,f103])).

fof(f84,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f60])).

fof(f885,plain,
    ( ~ v2_compts_1(sK8,k1_pre_topc(sK6,sK7))
    | sP0(k1_pre_topc(sK6,sK7),sK8) ),
    inference(superposition,[],[f102,f862])).

fof(f862,plain,(
    sK8 = sK9(k1_pre_topc(sK6,sK7),sK8) ),
    inference(resolution,[],[f857,f486])).

fof(f486,plain,(
    ! [X1] :
      ( ~ sP1(sK8,X1,sK6)
      | sK8 = sK9(X1,sK8) ) ),
    inference(resolution,[],[f178,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | sK9(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f178,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK8)
      | ~ sP1(sK8,X0,sK6) ) ),
    inference(resolution,[],[f88,f98])).

fof(f102,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ v2_compts_1(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f591,plain,
    ( v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))
    | ~ sP3(sK6,k1_pre_topc(sK6,sK7),sK8) ),
    inference(resolution,[],[f580,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(X2,X1)
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( ( v4_pre_topc(X2,X1)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ v4_pre_topc(X2,X1) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f580,plain,(
    sP2(sK8,k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f579,f293])).

fof(f293,plain,(
    sK8 = k3_xboole_0(sK7,sK8) ),
    inference(superposition,[],[f169,f122])).

fof(f122,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f169,plain,(
    sK8 = k3_xboole_0(sK8,sK7) ),
    inference(resolution,[],[f86,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f579,plain,(
    sP2(k3_xboole_0(sK7,sK8),k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f578,f122])).

fof(f578,plain,(
    sP2(k3_xboole_0(sK8,sK7),k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f577,f306])).

fof(f577,plain,(
    sP2(k3_xboole_0(sK8,k2_struct_0(k1_pre_topc(sK6,sK7))),k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f576,f122])).

fof(f576,plain,(
    sP2(k3_xboole_0(k2_struct_0(k1_pre_topc(sK6,sK7)),sK8),k1_pre_topc(sK6,sK7),sK6) ),
    inference(forward_demodulation,[],[f568,f526])).

fof(f526,plain,(
    ! [X2] : k9_subset_1(sK7,sK8,X2) = k3_xboole_0(X2,sK8) ),
    inference(subsumption_resolution,[],[f523,f166])).

fof(f523,plain,(
    ! [X2] :
      ( k9_subset_1(sK7,sK8,X2) = k3_xboole_0(X2,sK8)
      | ~ m1_subset_1(sK8,k1_zfmisc_1(sK7)) ) ),
    inference(superposition,[],[f183,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f183,plain,(
    ! [X1] : k9_subset_1(sK7,X1,sK8) = k3_xboole_0(X1,sK8) ),
    inference(resolution,[],[f166,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f568,plain,(
    sP2(k9_subset_1(sK7,sK8,k2_struct_0(k1_pre_topc(sK6,sK7))),k1_pre_topc(sK6,sK7),sK6) ),
    inference(superposition,[],[f244,f203])).

fof(f244,plain,(
    ! [X3] : sP2(k9_subset_1(u1_struct_0(X3),sK8,k2_struct_0(X3)),X3,sK6) ),
    inference(subsumption_resolution,[],[f227,f87])).

fof(f87,plain,(
    v4_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f60])).

fof(f227,plain,(
    ! [X3] :
      ( sP2(k9_subset_1(u1_struct_0(X3),sK8,k2_struct_0(X3)),X3,sK6)
      | ~ v4_pre_topc(sK8,sK6) ) ),
    inference(resolution,[],[f84,f134])).

fof(f134,plain,(
    ! [X2,X3,X1] :
      ( sP2(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X2)
      | ~ v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
      | ~ v4_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( k9_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k2_struct_0(X1)) = X0
          & v4_pre_topc(sK10(X0,X1,X2),X2)
          & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0
          & v4_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( k9_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k2_struct_0(X1)) = X0
        & v4_pre_topc(sK10(X0,X1,X2),X2)
        & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0
            | ~ v4_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0
            & v4_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ! [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
            & v4_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:56:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (32110)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.50  % (32106)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.50  % (32101)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (32106)Refutation not found, incomplete strategy% (32106)------------------------------
% 0.22/0.50  % (32106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (32124)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (32122)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (32115)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (32103)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (32113)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (32106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (32106)Memory used [KB]: 10618
% 0.22/0.51  % (32106)Time elapsed: 0.094 s
% 0.22/0.51  % (32106)------------------------------
% 0.22/0.51  % (32106)------------------------------
% 0.22/0.52  % (32114)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.52  % (32105)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (32109)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (32105)Refutation not found, incomplete strategy% (32105)------------------------------
% 0.22/0.52  % (32105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32105)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32105)Memory used [KB]: 6140
% 0.22/0.52  % (32105)Time elapsed: 0.107 s
% 0.22/0.52  % (32105)------------------------------
% 0.22/0.52  % (32105)------------------------------
% 0.22/0.52  % (32107)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (32119)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (32123)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (32121)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.53  % (32118)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (32112)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (32102)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (32120)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (32108)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.54  % (32100)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (32117)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.54  % (32100)Refutation not found, incomplete strategy% (32100)------------------------------
% 0.22/0.54  % (32100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (32100)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (32100)Memory used [KB]: 10746
% 0.22/0.54  % (32100)Time elapsed: 0.129 s
% 0.22/0.54  % (32100)------------------------------
% 0.22/0.54  % (32100)------------------------------
% 0.22/0.55  % (32125)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.57  % (32111)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.57  % (32104)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.59  % (32116)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.83/0.60  % (32111)Refutation not found, incomplete strategy% (32111)------------------------------
% 1.83/0.60  % (32111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.83/0.60  % (32111)Termination reason: Refutation not found, incomplete strategy
% 1.83/0.60  
% 1.83/0.60  % (32111)Memory used [KB]: 10874
% 1.83/0.60  % (32111)Time elapsed: 0.146 s
% 1.83/0.60  % (32111)------------------------------
% 1.83/0.60  % (32111)------------------------------
% 1.83/0.61  % (32108)Refutation found. Thanks to Tanya!
% 1.83/0.61  % SZS status Theorem for theBenchmark
% 1.83/0.61  % SZS output start Proof for theBenchmark
% 1.83/0.61  fof(f1625,plain,(
% 1.83/0.61    $false),
% 1.83/0.61    inference(subsumption_resolution,[],[f1624,f166])).
% 1.83/0.61  fof(f166,plain,(
% 1.83/0.61    m1_subset_1(sK8,k1_zfmisc_1(sK7))),
% 1.83/0.61    inference(resolution,[],[f86,f130])).
% 1.83/0.61  fof(f130,plain,(
% 1.83/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.83/0.61    inference(cnf_transformation,[],[f80])).
% 1.83/0.61  fof(f80,plain,(
% 1.83/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.83/0.61    inference(nnf_transformation,[],[f8])).
% 2.02/0.63  fof(f8,axiom,(
% 2.02/0.63    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.02/0.63  fof(f86,plain,(
% 2.02/0.63    r1_tarski(sK8,sK7)),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f60,plain,(
% 2.02/0.63    ((~v2_compts_1(sK8,sK6) & v4_pre_topc(sK8,sK6) & r1_tarski(sK8,sK7) & v2_compts_1(sK7,sK6) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6)),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f59,f58,f57])).
% 2.02/0.63  fof(f57,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v2_compts_1(X2,sK6) & v4_pre_topc(X2,sK6) & r1_tarski(X2,X1) & v2_compts_1(X1,sK6) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6) & v2_pre_topc(sK6))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f58,plain,(
% 2.02/0.63    ? [X1] : (? [X2] : (~v2_compts_1(X2,sK6) & v4_pre_topc(X2,sK6) & r1_tarski(X2,X1) & v2_compts_1(X1,sK6) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) => (? [X2] : (~v2_compts_1(X2,sK6) & v4_pre_topc(X2,sK6) & r1_tarski(X2,sK7) & v2_compts_1(sK7,sK6) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f59,plain,(
% 2.02/0.63    ? [X2] : (~v2_compts_1(X2,sK6) & v4_pre_topc(X2,sK6) & r1_tarski(X2,sK7) & v2_compts_1(sK7,sK6) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) => (~v2_compts_1(sK8,sK6) & v4_pre_topc(sK8,sK6) & r1_tarski(sK8,sK7) & v2_compts_1(sK7,sK6) & m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6))))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f25,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (? [X2] : (~v2_compts_1(X2,X0) & v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f24])).
% 2.02/0.63  fof(f24,plain,(
% 2.02/0.63    ? [X0] : (? [X1] : (? [X2] : ((~v2_compts_1(X2,X0) & (v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f23])).
% 2.02/0.63  fof(f23,negated_conjecture,(
% 2.02/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 2.02/0.63    inference(negated_conjecture,[],[f22])).
% 2.02/0.63  fof(f22,conjecture,(
% 2.02/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & r1_tarski(X2,X1) & v2_compts_1(X1,X0)) => v2_compts_1(X2,X0)))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).
% 2.02/0.63  fof(f1624,plain,(
% 2.02/0.63    ~m1_subset_1(sK8,k1_zfmisc_1(sK7))),
% 2.02/0.63    inference(forward_demodulation,[],[f1623,f203])).
% 2.02/0.63  fof(f203,plain,(
% 2.02/0.63    sK7 = u1_struct_0(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f188,f82])).
% 2.02/0.63  fof(f82,plain,(
% 2.02/0.63    l1_pre_topc(sK6)),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f188,plain,(
% 2.02/0.63    sK7 = u1_struct_0(k1_pre_topc(sK6,sK7)) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(resolution,[],[f83,f111])).
% 2.02/0.63  fof(f111,plain,(
% 2.02/0.63    ( ! [X0,X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f34])).
% 2.02/0.63  fof(f34,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f15])).
% 2.02/0.63  fof(f15,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 2.02/0.63  fof(f83,plain,(
% 2.02/0.63    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f1623,plain,(
% 2.02/0.63    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))),
% 2.02/0.63    inference(subsumption_resolution,[],[f1621,f207])).
% 2.02/0.63  fof(f207,plain,(
% 2.02/0.63    m1_pre_topc(k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(subsumption_resolution,[],[f193,f82])).
% 2.02/0.63  fof(f193,plain,(
% 2.02/0.63    m1_pre_topc(k1_pre_topc(sK6,sK7),sK6) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(resolution,[],[f83,f125])).
% 2.02/0.63  fof(f125,plain,(
% 2.02/0.63    ( ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f45])).
% 2.02/0.63  fof(f45,plain,(
% 2.02/0.63    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f44])).
% 2.02/0.63  fof(f44,plain,(
% 2.02/0.63    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f11])).
% 2.02/0.63  fof(f11,axiom,(
% 2.02/0.63    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 2.02/0.63  fof(f1621,plain,(
% 2.02/0.63    ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))) | ~m1_pre_topc(k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(resolution,[],[f1619,f151])).
% 2.02/0.63  fof(f151,plain,(
% 2.02/0.63    ( ! [X6,X5] : (sP3(sK6,X5,X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5))) | ~m1_pre_topc(X5,sK6)) )),
% 2.02/0.63    inference(resolution,[],[f82,f110])).
% 2.02/0.63  fof(f110,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f53])).
% 2.02/0.63  fof(f53,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (sP3(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(definition_folding,[],[f33,f52,f51])).
% 2.02/0.63  fof(f51,plain,(
% 2.02/0.63    ! [X2,X1,X0] : (sP2(X2,X1,X0) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.02/0.63  fof(f52,plain,(
% 2.02/0.63    ! [X0,X1,X2] : ((v4_pre_topc(X2,X1) <=> sP2(X2,X1,X0)) | ~sP3(X0,X1,X2))),
% 2.02/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.02/0.63  fof(f33,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f17])).
% 2.02/0.63  fof(f17,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 2.02/0.63  fof(f1619,plain,(
% 2.02/0.63    ~sP3(sK6,k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(subsumption_resolution,[],[f591,f1122])).
% 2.02/0.63  fof(f1122,plain,(
% 2.02/0.63    ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f1118,f1056])).
% 2.02/0.63  fof(f1056,plain,(
% 2.02/0.63    v2_compts_1(sK7,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f1055,f141])).
% 2.02/0.63  fof(f141,plain,(
% 2.02/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.02/0.63    inference(equality_resolution,[],[f126])).
% 2.02/0.63  fof(f126,plain,(
% 2.02/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.02/0.63    inference(cnf_transformation,[],[f79])).
% 2.02/0.63  fof(f79,plain,(
% 2.02/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.63    inference(flattening,[],[f78])).
% 2.02/0.63  fof(f78,plain,(
% 2.02/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.02/0.63    inference(nnf_transformation,[],[f2])).
% 2.02/0.63  fof(f2,axiom,(
% 2.02/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.02/0.63  fof(f1055,plain,(
% 2.02/0.63    v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) | ~r1_tarski(sK7,sK7)),
% 2.02/0.63    inference(resolution,[],[f819,f130])).
% 2.02/0.63  fof(f819,plain,(
% 2.02/0.63    ~m1_subset_1(sK7,k1_zfmisc_1(sK7)) | v2_compts_1(sK7,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(forward_demodulation,[],[f817,f203])).
% 2.02/0.63  fof(f817,plain,(
% 2.02/0.63    v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))),
% 2.02/0.63    inference(resolution,[],[f816,f133])).
% 2.02/0.63  fof(f133,plain,(
% 2.02/0.63    ( ! [X0,X3] : (v2_compts_1(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X3)) )),
% 2.02/0.63    inference(equality_resolution,[],[f99])).
% 2.02/0.63  fof(f99,plain,(
% 2.02/0.63    ( ! [X0,X3,X1] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~sP0(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f67])).
% 2.02/0.63  fof(f67,plain,(
% 2.02/0.63    ! [X0,X1] : ((sP0(X0,X1) | (~v2_compts_1(sK9(X0,X1),X0) & sK9(X0,X1) = X1 & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f65,f66])).
% 2.02/0.63  fof(f66,plain,(
% 2.02/0.63    ! [X1,X0] : (? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v2_compts_1(sK9(X0,X1),X0) & sK9(X0,X1) = X1 & m1_subset_1(sK9(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f65,plain,(
% 2.02/0.63    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (~v2_compts_1(X2,X0) & X1 = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v2_compts_1(X3,X0) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0,X1)))),
% 2.02/0.63    inference(rectify,[],[f64])).
% 2.02/0.63  fof(f64,plain,(
% 2.02/0.63    ! [X1,X2] : ((sP0(X1,X2) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X1,X2)))),
% 2.02/0.63    inference(nnf_transformation,[],[f48])).
% 2.02/0.63  fof(f48,plain,(
% 2.02/0.63    ! [X1,X2] : (sP0(X1,X2) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.02/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.02/0.63  fof(f816,plain,(
% 2.02/0.63    sP0(k1_pre_topc(sK6,sK7),sK7)),
% 2.02/0.63    inference(subsumption_resolution,[],[f814,f85])).
% 2.02/0.63  fof(f85,plain,(
% 2.02/0.63    v2_compts_1(sK7,sK6)),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f814,plain,(
% 2.02/0.63    sP0(k1_pre_topc(sK6,sK7),sK7) | ~v2_compts_1(sK7,sK6)),
% 2.02/0.63    inference(resolution,[],[f811,f97])).
% 2.02/0.63  fof(f97,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (sP0(X1,X0) | ~v2_compts_1(X0,X2) | ~sP1(X0,X1,X2)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f63])).
% 2.02/0.63  fof(f63,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (((v2_compts_1(X0,X2) | ~sP0(X1,X0)) & (sP0(X1,X0) | ~v2_compts_1(X0,X2))) | ~sP1(X0,X1,X2))),
% 2.02/0.63    inference(rectify,[],[f62])).
% 2.02/0.63  fof(f62,plain,(
% 2.02/0.63    ! [X2,X1,X0] : (((v2_compts_1(X2,X0) | ~sP0(X1,X2)) & (sP0(X1,X2) | ~v2_compts_1(X2,X0))) | ~sP1(X2,X1,X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f49])).
% 2.02/0.63  fof(f49,plain,(
% 2.02/0.63    ! [X2,X1,X0] : ((v2_compts_1(X2,X0) <=> sP0(X1,X2)) | ~sP1(X2,X1,X0))),
% 2.02/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.02/0.63  fof(f811,plain,(
% 2.02/0.63    sP1(sK7,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(subsumption_resolution,[],[f810,f141])).
% 2.02/0.63  fof(f810,plain,(
% 2.02/0.63    ~r1_tarski(sK7,sK7) | sP1(sK7,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f806,f306])).
% 2.02/0.63  fof(f306,plain,(
% 2.02/0.63    sK7 = k2_struct_0(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f305,f82])).
% 2.02/0.63  fof(f305,plain,(
% 2.02/0.63    sK7 = k2_struct_0(k1_pre_topc(sK6,sK7)) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(subsumption_resolution,[],[f304,f83])).
% 2.02/0.63  fof(f304,plain,(
% 2.02/0.63    sK7 = k2_struct_0(k1_pre_topc(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(subsumption_resolution,[],[f297,f206])).
% 2.02/0.63  fof(f206,plain,(
% 2.02/0.63    v1_pre_topc(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f192,f82])).
% 2.02/0.63  fof(f192,plain,(
% 2.02/0.63    v1_pre_topc(k1_pre_topc(sK6,sK7)) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(resolution,[],[f83,f124])).
% 2.02/0.63  fof(f124,plain,(
% 2.02/0.63    ( ! [X0,X1] : (v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f45])).
% 2.02/0.63  fof(f297,plain,(
% 2.02/0.63    sK7 = k2_struct_0(k1_pre_topc(sK6,sK7)) | ~v1_pre_topc(k1_pre_topc(sK6,sK7)) | ~m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) | ~l1_pre_topc(sK6)),
% 2.02/0.63    inference(resolution,[],[f207,f138])).
% 2.02/0.63  fof(f138,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(equality_resolution,[],[f119])).
% 2.02/0.63  fof(f119,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f77])).
% 2.02/0.63  fof(f77,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f40])).
% 2.02/0.63  fof(f40,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f39])).
% 2.02/0.63  fof(f39,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f9])).
% 2.02/0.63  fof(f9,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 2.02/0.63  fof(f806,plain,(
% 2.02/0.63    ~r1_tarski(sK7,k2_struct_0(k1_pre_topc(sK6,sK7))) | sP1(sK7,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(resolution,[],[f202,f207])).
% 2.02/0.63  fof(f202,plain,(
% 2.02/0.63    ( ! [X1] : (~m1_pre_topc(X1,sK6) | ~r1_tarski(sK7,k2_struct_0(X1)) | sP1(sK7,X1,sK6)) )),
% 2.02/0.63    inference(subsumption_resolution,[],[f186,f82])).
% 2.02/0.63  fof(f186,plain,(
% 2.02/0.63    ( ! [X1] : (sP1(sK7,X1,sK6) | ~r1_tarski(sK7,k2_struct_0(X1)) | ~m1_pre_topc(X1,sK6) | ~l1_pre_topc(sK6)) )),
% 2.02/0.63    inference(resolution,[],[f83,f103])).
% 2.02/0.63  fof(f103,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f50])).
% 2.02/0.63  fof(f50,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (sP1(X2,X1,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(definition_folding,[],[f32,f49,f48])).
% 2.02/0.63  fof(f32,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f31])).
% 2.02/0.63  fof(f31,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f19])).
% 2.02/0.63  fof(f19,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 2.02/0.63  fof(f1118,plain,(
% 2.02/0.63    ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) | ~v2_compts_1(sK7,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(resolution,[],[f895,f465])).
% 2.02/0.63  fof(f465,plain,(
% 2.02/0.63    v1_compts_1(k1_pre_topc(sK6,sK7)) | ~v2_compts_1(sK7,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f458,f298])).
% 2.02/0.63  fof(f298,plain,(
% 2.02/0.63    l1_pre_topc(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(resolution,[],[f207,f148])).
% 2.02/0.63  fof(f148,plain,(
% 2.02/0.63    ( ! [X0] : (~m1_pre_topc(X0,sK6) | l1_pre_topc(X0)) )),
% 2.02/0.63    inference(resolution,[],[f82,f95])).
% 2.02/0.63  fof(f95,plain,(
% 2.02/0.63    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f29])).
% 2.02/0.63  fof(f29,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f13])).
% 2.02/0.63  fof(f13,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.02/0.63  fof(f458,plain,(
% 2.02/0.63    ~v2_compts_1(sK7,k1_pre_topc(sK6,sK7)) | v1_compts_1(k1_pre_topc(sK6,sK7)) | ~l1_pre_topc(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(superposition,[],[f94,f306])).
% 2.02/0.63  fof(f94,plain,(
% 2.02/0.63    ( ! [X0] : (v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f61])).
% 2.02/0.63  fof(f61,plain,(
% 2.02/0.63    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(nnf_transformation,[],[f28])).
% 2.02/0.63  fof(f28,plain,(
% 2.02/0.63    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f18])).
% 2.02/0.63  fof(f18,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 2.02/0.63  fof(f895,plain,(
% 2.02/0.63    ~v1_compts_1(k1_pre_topc(sK6,sK7)) | ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f894,f166])).
% 2.02/0.63  fof(f894,plain,(
% 2.02/0.63    ~m1_subset_1(sK8,k1_zfmisc_1(sK7)) | ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) | ~v1_compts_1(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(forward_demodulation,[],[f893,f203])).
% 2.02/0.63  fof(f893,plain,(
% 2.02/0.63    ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) | ~v1_compts_1(k1_pre_topc(sK6,sK7)) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7))))),
% 2.02/0.63    inference(subsumption_resolution,[],[f889,f298])).
% 2.02/0.63  fof(f889,plain,(
% 2.02/0.63    ~v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) | ~v1_compts_1(k1_pre_topc(sK6,sK7)) | ~m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK6,sK7)))) | ~l1_pre_topc(k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(resolution,[],[f888,f118])).
% 2.02/0.63  fof(f118,plain,(
% 2.02/0.63    ( ! [X0,X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f38])).
% 2.02/0.63  fof(f38,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : (v2_compts_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v1_compts_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(flattening,[],[f37])).
% 2.02/0.63  fof(f37,plain,(
% 2.02/0.63    ! [X0] : (! [X1] : ((v2_compts_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v1_compts_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/0.63    inference(ennf_transformation,[],[f21])).
% 2.02/0.63  fof(f21,axiom,(
% 2.02/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v1_compts_1(X0)) => v2_compts_1(X1,X0))))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).
% 2.02/0.63  fof(f888,plain,(
% 2.02/0.63    ~v2_compts_1(sK8,k1_pre_topc(sK6,sK7))),
% 2.02/0.63    inference(subsumption_resolution,[],[f885,f865])).
% 2.02/0.63  fof(f865,plain,(
% 2.02/0.63    ~sP0(k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(subsumption_resolution,[],[f864,f88])).
% 2.02/0.63  fof(f88,plain,(
% 2.02/0.63    ~v2_compts_1(sK8,sK6)),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f864,plain,(
% 2.02/0.63    v2_compts_1(sK8,sK6) | ~sP0(k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(resolution,[],[f857,f98])).
% 2.02/0.63  fof(f98,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v2_compts_1(X0,X2) | ~sP0(X1,X0) | ~sP1(X0,X1,X2)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f63])).
% 2.02/0.63  fof(f857,plain,(
% 2.02/0.63    sP1(sK8,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(subsumption_resolution,[],[f856,f86])).
% 2.02/0.63  fof(f856,plain,(
% 2.02/0.63    ~r1_tarski(sK8,sK7) | sP1(sK8,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f852,f306])).
% 2.02/0.63  fof(f852,plain,(
% 2.02/0.63    ~r1_tarski(sK8,k2_struct_0(k1_pre_topc(sK6,sK7))) | sP1(sK8,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(resolution,[],[f234,f207])).
% 2.02/0.63  fof(f234,plain,(
% 2.02/0.63    ( ! [X1] : (~m1_pre_topc(X1,sK6) | ~r1_tarski(sK8,k2_struct_0(X1)) | sP1(sK8,X1,sK6)) )),
% 2.02/0.63    inference(subsumption_resolution,[],[f218,f82])).
% 2.02/0.63  fof(f218,plain,(
% 2.02/0.63    ( ! [X1] : (sP1(sK8,X1,sK6) | ~r1_tarski(sK8,k2_struct_0(X1)) | ~m1_pre_topc(X1,sK6) | ~l1_pre_topc(sK6)) )),
% 2.02/0.63    inference(resolution,[],[f84,f103])).
% 2.02/0.63  fof(f84,plain,(
% 2.02/0.63    m1_subset_1(sK8,k1_zfmisc_1(u1_struct_0(sK6)))),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f885,plain,(
% 2.02/0.63    ~v2_compts_1(sK8,k1_pre_topc(sK6,sK7)) | sP0(k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(superposition,[],[f102,f862])).
% 2.02/0.63  fof(f862,plain,(
% 2.02/0.63    sK8 = sK9(k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(resolution,[],[f857,f486])).
% 2.02/0.63  fof(f486,plain,(
% 2.02/0.63    ( ! [X1] : (~sP1(sK8,X1,sK6) | sK8 = sK9(X1,sK8)) )),
% 2.02/0.63    inference(resolution,[],[f178,f101])).
% 2.02/0.63  fof(f101,plain,(
% 2.02/0.63    ( ! [X0,X1] : (sP0(X0,X1) | sK9(X0,X1) = X1) )),
% 2.02/0.63    inference(cnf_transformation,[],[f67])).
% 2.02/0.63  fof(f178,plain,(
% 2.02/0.63    ( ! [X0] : (~sP0(X0,sK8) | ~sP1(sK8,X0,sK6)) )),
% 2.02/0.63    inference(resolution,[],[f88,f98])).
% 2.02/0.63  fof(f102,plain,(
% 2.02/0.63    ( ! [X0,X1] : (sP0(X0,X1) | ~v2_compts_1(sK9(X0,X1),X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f67])).
% 2.02/0.63  fof(f591,plain,(
% 2.02/0.63    v4_pre_topc(sK8,k1_pre_topc(sK6,sK7)) | ~sP3(sK6,k1_pre_topc(sK6,sK7),sK8)),
% 2.02/0.63    inference(resolution,[],[f580,f105])).
% 2.02/0.63  fof(f105,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (v4_pre_topc(X2,X1) | ~sP2(X2,X1,X0) | ~sP3(X0,X1,X2)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f68])).
% 2.02/0.63  fof(f68,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (((v4_pre_topc(X2,X1) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~v4_pre_topc(X2,X1))) | ~sP3(X0,X1,X2))),
% 2.02/0.63    inference(nnf_transformation,[],[f52])).
% 2.02/0.63  fof(f580,plain,(
% 2.02/0.63    sP2(sK8,k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f579,f293])).
% 2.02/0.63  fof(f293,plain,(
% 2.02/0.63    sK8 = k3_xboole_0(sK7,sK8)),
% 2.02/0.63    inference(superposition,[],[f169,f122])).
% 2.02/0.63  fof(f122,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f1])).
% 2.02/0.63  fof(f1,axiom,(
% 2.02/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.02/0.63  fof(f169,plain,(
% 2.02/0.63    sK8 = k3_xboole_0(sK8,sK7)),
% 2.02/0.63    inference(resolution,[],[f86,f123])).
% 2.02/0.63  fof(f123,plain,(
% 2.02/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.02/0.63    inference(cnf_transformation,[],[f43])).
% 2.02/0.63  fof(f43,plain,(
% 2.02/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.02/0.63    inference(ennf_transformation,[],[f3])).
% 2.02/0.63  fof(f3,axiom,(
% 2.02/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.02/0.63  fof(f579,plain,(
% 2.02/0.63    sP2(k3_xboole_0(sK7,sK8),k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f578,f122])).
% 2.02/0.63  fof(f578,plain,(
% 2.02/0.63    sP2(k3_xboole_0(sK8,sK7),k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f577,f306])).
% 2.02/0.63  fof(f577,plain,(
% 2.02/0.63    sP2(k3_xboole_0(sK8,k2_struct_0(k1_pre_topc(sK6,sK7))),k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f576,f122])).
% 2.02/0.63  fof(f576,plain,(
% 2.02/0.63    sP2(k3_xboole_0(k2_struct_0(k1_pre_topc(sK6,sK7)),sK8),k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(forward_demodulation,[],[f568,f526])).
% 2.02/0.63  fof(f526,plain,(
% 2.02/0.63    ( ! [X2] : (k9_subset_1(sK7,sK8,X2) = k3_xboole_0(X2,sK8)) )),
% 2.02/0.63    inference(subsumption_resolution,[],[f523,f166])).
% 2.02/0.63  fof(f523,plain,(
% 2.02/0.63    ( ! [X2] : (k9_subset_1(sK7,sK8,X2) = k3_xboole_0(X2,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(sK7))) )),
% 2.02/0.63    inference(superposition,[],[f183,f132])).
% 2.02/0.63  fof(f132,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f47])).
% 2.02/0.63  fof(f47,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f4])).
% 2.02/0.63  fof(f4,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 2.02/0.63  fof(f183,plain,(
% 2.02/0.63    ( ! [X1] : (k9_subset_1(sK7,X1,sK8) = k3_xboole_0(X1,sK8)) )),
% 2.02/0.63    inference(resolution,[],[f166,f131])).
% 2.02/0.63  fof(f131,plain,(
% 2.02/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f46])).
% 2.02/0.63  fof(f46,plain,(
% 2.02/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.02/0.63    inference(ennf_transformation,[],[f7])).
% 2.02/0.63  fof(f7,axiom,(
% 2.02/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.02/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.02/0.63  fof(f568,plain,(
% 2.02/0.63    sP2(k9_subset_1(sK7,sK8,k2_struct_0(k1_pre_topc(sK6,sK7))),k1_pre_topc(sK6,sK7),sK6)),
% 2.02/0.63    inference(superposition,[],[f244,f203])).
% 2.02/0.63  fof(f244,plain,(
% 2.02/0.63    ( ! [X3] : (sP2(k9_subset_1(u1_struct_0(X3),sK8,k2_struct_0(X3)),X3,sK6)) )),
% 2.02/0.63    inference(subsumption_resolution,[],[f227,f87])).
% 2.02/0.63  fof(f87,plain,(
% 2.02/0.63    v4_pre_topc(sK8,sK6)),
% 2.02/0.63    inference(cnf_transformation,[],[f60])).
% 2.02/0.63  fof(f227,plain,(
% 2.02/0.63    ( ! [X3] : (sP2(k9_subset_1(u1_struct_0(X3),sK8,k2_struct_0(X3)),X3,sK6) | ~v4_pre_topc(sK8,sK6)) )),
% 2.02/0.63    inference(resolution,[],[f84,f134])).
% 2.02/0.63  fof(f134,plain,(
% 2.02/0.63    ( ! [X2,X3,X1] : (sP2(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1,X2) | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.02/0.63    inference(equality_resolution,[],[f109])).
% 2.02/0.63  fof(f109,plain,(
% 2.02/0.63    ( ! [X2,X0,X3,X1] : (sP2(X0,X1,X2) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.02/0.63    inference(cnf_transformation,[],[f72])).
% 2.02/0.63  fof(f72,plain,(
% 2.02/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((k9_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k2_struct_0(X1)) = X0 & v4_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP2(X0,X1,X2)))),
% 2.02/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f70,f71])).
% 2.02/0.63  fof(f71,plain,(
% 2.02/0.63    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (k9_subset_1(u1_struct_0(X1),sK10(X0,X1,X2),k2_struct_0(X1)) = X0 & v4_pre_topc(sK10(X0,X1,X2),X2) & m1_subset_1(sK10(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 2.02/0.63    introduced(choice_axiom,[])).
% 2.02/0.63  fof(f70,plain,(
% 2.02/0.63    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X0 | ~v4_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X0 & v4_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP2(X0,X1,X2)))),
% 2.02/0.63    inference(rectify,[],[f69])).
% 2.02/0.63  fof(f69,plain,(
% 2.02/0.63    ! [X2,X1,X0] : ((sP2(X2,X1,X0) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP2(X2,X1,X0)))),
% 2.02/0.63    inference(nnf_transformation,[],[f51])).
% 2.02/0.63  % SZS output end Proof for theBenchmark
% 2.02/0.63  % (32108)------------------------------
% 2.02/0.63  % (32108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.02/0.63  % (32108)Termination reason: Refutation
% 2.02/0.63  
% 2.02/0.63  % (32108)Memory used [KB]: 2302
% 2.02/0.63  % (32108)Time elapsed: 0.203 s
% 2.02/0.63  % (32108)------------------------------
% 2.02/0.63  % (32108)------------------------------
% 2.02/0.63  % (32099)Success in time 0.27 s
%------------------------------------------------------------------------------
