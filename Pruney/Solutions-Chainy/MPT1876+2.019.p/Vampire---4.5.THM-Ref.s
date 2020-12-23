%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 (3274 expanded)
%              Number of leaves         :   25 ( 884 expanded)
%              Depth                    :   38
%              Number of atoms          :  648 (22488 expanded)
%              Number of equality atoms :   53 ( 483 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(subsumption_resolution,[],[f743,f720])).

fof(f720,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(backward_demodulation,[],[f305,f711])).

fof(f711,plain,(
    sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f710,f188])).

fof(f188,plain,
    ( ~ v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f187,f78])).

fof(f78,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f187,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(k1_tarski(sK6(sK4))) ),
    inference(subsumption_resolution,[],[f186,f74])).

fof(f74,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v1_zfmisc_1(sK4)
      | ~ v2_tex_2(sK4,sK3) )
    & ( v1_zfmisc_1(sK4)
      | v2_tex_2(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & ~ v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_tdlat_3(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v2_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,sK3) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_tdlat_3(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v2_tex_2(X1,sK3) )
        & ( v1_zfmisc_1(X1)
          | v2_tex_2(X1,sK3) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK4)
        | ~ v2_tex_2(sK4,sK3) )
      & ( v1_zfmisc_1(sK4)
        | v2_tex_2(sK4,sK3) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v2_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v2_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f186,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(k1_tarski(sK6(sK4))) ),
    inference(resolution,[],[f166,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f166,plain,(
    r1_tarski(k1_tarski(sK6(sK4)),sK4) ),
    inference(resolution,[],[f142,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f142,plain,(
    r2_hidden(sK6(sK4),sK4) ),
    inference(resolution,[],[f74,f94])).

fof(f94,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f710,plain,
    ( v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f709,f374])).

fof(f374,plain,
    ( sP0(sK4,sK3)
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f314,f155])).

fof(f155,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | sP0(sK4,sK3) ),
    inference(subsumption_resolution,[],[f154,f70])).

fof(f70,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f154,plain,
    ( sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f153,f71])).

fof(f71,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f153,plain,
    ( sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f152,f73])).

fof(f73,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f152,plain,
    ( sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f148,f74])).

fof(f148,plain,
    ( sP0(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f75,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP0(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f35,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).

fof(f75,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f51])).

fof(f314,plain,
    ( v2_tex_2(sK4,sK3)
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f311,f78])).

fof(f311,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | v2_tex_2(sK4,sK3)
    | v1_xboole_0(k1_tarski(sK6(sK4))) ),
    inference(resolution,[],[f177,f166])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK4)
      | sK4 = X0
      | v2_tex_2(sK4,sK3)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f176,f74])).

fof(f176,plain,(
    ! [X0] :
      ( v2_tex_2(sK4,sK3)
      | sK4 = X0
      | ~ r1_tarski(X0,sK4)
      | v1_xboole_0(sK4)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f76,f79])).

fof(f76,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f709,plain,
    ( v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK6(sK4))
    | ~ sP0(sK4,sK3) ),
    inference(superposition,[],[f638,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK5(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK5(X0,X1)) = X0
        & m1_pre_topc(sK5(X0,X1),X1)
        & v1_tdlat_3(sK5(X0,X1))
        & ~ v2_struct_0(sK5(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK5(X0,X1)) = X0
        & m1_pre_topc(sK5(X0,X1),X1)
        & v1_tdlat_3(sK5(X0,X1))
        & ~ v2_struct_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP0(X1,X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f638,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5(sK4,sK3)))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f637,f539])).

fof(f539,plain,
    ( l1_struct_0(sK5(sK4,sK3))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f432,f80])).

fof(f80,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f432,plain,
    ( l1_pre_topc(sK5(sK4,sK3))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f374,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ sP0(X0,sK3)
      | l1_pre_topc(sK5(X0,sK3)) ) ),
    inference(resolution,[],[f131,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK5(X0,X1),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f131,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK3)
      | l1_pre_topc(X3) ) ),
    inference(resolution,[],[f73,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f637,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | v1_zfmisc_1(u1_struct_0(sK5(sK4,sK3)))
    | ~ l1_struct_0(sK5(sK4,sK3)) ),
    inference(resolution,[],[f627,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f627,plain,
    ( v7_struct_0(sK5(sK4,sK3))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(subsumption_resolution,[],[f626,f433])).

fof(f433,plain,
    ( ~ v2_struct_0(sK5(sK4,sK3))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f374,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f626,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f625,f434])).

fof(f434,plain,
    ( v1_tdlat_3(sK5(sK4,sK3))
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f374,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK5(X0,X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f625,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_tdlat_3(sK5(sK4,sK3))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f624,f70])).

fof(f624,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_tdlat_3(sK5(sK4,sK3))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f623,f71])).

% (13131)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f623,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_tdlat_3(sK5(sK4,sK3))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f622,f72])).

fof(f72,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f622,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_tdlat_3(sK5(sK4,sK3))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f620,f73])).

fof(f620,plain,
    ( sK4 = k1_tarski(sK6(sK4))
    | ~ v1_tdlat_3(sK5(sK4,sK3))
    | v7_struct_0(sK5(sK4,sK3))
    | v2_struct_0(sK5(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f435,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v7_struct_0(X1)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f435,plain,
    ( m1_pre_topc(sK5(sK4,sK3),sK3)
    | sK4 = k1_tarski(sK6(sK4)) ),
    inference(resolution,[],[f374,f89])).

fof(f305,plain,(
    v2_tex_2(k1_tarski(sK6(sK4)),sK3) ),
    inference(subsumption_resolution,[],[f304,f156])).

fof(f156,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f150,f74])).

fof(f150,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f75,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f304,plain,
    ( v2_tex_2(k1_tarski(sK6(sK4)),sK3)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f300,f284])).

fof(f284,plain,(
    m1_subset_1(sK6(sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f278,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f278,plain,(
    r2_hidden(sK6(sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f268,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ r2_hidden(X1,X0)
        | ~ r2_hidden(X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_hidden(X1,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X1,X3,X0] :
      ( ( sP1(X1,X3,X0)
        | ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,X0) )
      & ( ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
        | ~ sP1(X1,X3,X0) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X3,X0] :
      ( sP1(X1,X3,X0)
    <=> ( r2_hidden(X3,X1)
        & r2_hidden(X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f268,plain,(
    sP1(u1_struct_0(sK3),sK6(sK4),sK4) ),
    inference(resolution,[],[f205,f142])).

fof(f205,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK4)
      | sP1(u1_struct_0(sK3),X0,sK4) ) ),
    inference(resolution,[],[f202,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( sP1(X1,X4,X0)
      | ~ r2_hidden(X4,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( sP1(X1,sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ sP1(X1,X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( sP1(X1,X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ sP1(X1,sK7(X0,X1,X2),X0)
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( sP1(X1,sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ sP1(X1,X4,X0) )
            & ( sP1(X1,X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ~ sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( sP1(X1,X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ sP1(X1,X3,X0) )
            & ( sP1(X1,X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> sP1(X1,X3,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f202,plain,(
    sP2(sK4,u1_struct_0(sK3),sK4) ),
    inference(superposition,[],[f111,f170])).

fof(f170,plain,(
    sK4 = k3_xboole_0(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f149,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f149,plain,(
    r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(resolution,[],[f75,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f111,plain,(
    ! [X0,X1] : sP2(X0,X1,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP2(X0,X1,X2) )
      & ( sP2(X0,X1,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP2(X0,X1,X2) ) ),
    inference(definition_folding,[],[f2,f45,f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f300,plain,
    ( v2_tex_2(k1_tarski(sK6(sK4)),sK3)
    | ~ m1_subset_1(sK6(sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f286,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f286,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK6(sK4)),sK3) ),
    inference(resolution,[],[f284,f137])).

fof(f137,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) ) ),
    inference(subsumption_resolution,[],[f136,f70])).

fof(f136,plain,(
    ! [X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f129,f71])).

fof(f129,plain,(
    ! [X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f73,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f743,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f730,f77])).

fof(f77,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f730,plain,(
    v1_zfmisc_1(sK4) ),
    inference(backward_demodulation,[],[f369,f711])).

fof(f369,plain,(
    v1_zfmisc_1(k1_tarski(sK6(sK4))) ),
    inference(subsumption_resolution,[],[f368,f324])).

fof(f324,plain,(
    sP0(k1_tarski(sK6(sK4)),sK3) ),
    inference(subsumption_resolution,[],[f323,f70])).

fof(f323,plain,
    ( sP0(k1_tarski(sK6(sK4)),sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f322,f71])).

fof(f322,plain,
    ( sP0(k1_tarski(sK6(sK4)),sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f321,f73])).

fof(f321,plain,
    ( sP0(k1_tarski(sK6(sK4)),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f320,f78])).

fof(f320,plain,
    ( sP0(k1_tarski(sK6(sK4)),sK3)
    | v1_xboole_0(k1_tarski(sK6(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f316,f305])).

fof(f316,plain,
    ( sP0(k1_tarski(sK6(sK4)),sK3)
    | ~ v2_tex_2(k1_tarski(sK6(sK4)),sK3)
    | v1_xboole_0(k1_tarski(sK6(sK4)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f294,f91])).

fof(f294,plain,(
    m1_subset_1(k1_tarski(sK6(sK4)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(resolution,[],[f283,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f283,plain,(
    r1_tarski(k1_tarski(sK6(sK4)),u1_struct_0(sK3)) ),
    inference(resolution,[],[f278,f99])).

fof(f368,plain,
    ( v1_zfmisc_1(k1_tarski(sK6(sK4)))
    | ~ sP0(k1_tarski(sK6(sK4)),sK3) ),
    inference(superposition,[],[f365,f90])).

fof(f365,plain,(
    v1_zfmisc_1(u1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))) ),
    inference(subsumption_resolution,[],[f364,f335])).

fof(f335,plain,(
    l1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(resolution,[],[f325,f80])).

fof(f325,plain,(
    l1_pre_topc(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(resolution,[],[f324,f179])).

fof(f364,plain,
    ( v1_zfmisc_1(u1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)))
    | ~ l1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(resolution,[],[f358,f92])).

fof(f358,plain,(
    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(subsumption_resolution,[],[f357,f70])).

fof(f357,plain,
    ( v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f356,f71])).

fof(f356,plain,
    ( v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f355,f72])).

fof(f355,plain,
    ( v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f354,f73])).

fof(f354,plain,
    ( v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f353,f326])).

fof(f326,plain,(
    ~ v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(resolution,[],[f324,f87])).

fof(f353,plain,
    ( v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f351,f327])).

fof(f327,plain,(
    v1_tdlat_3(sK5(k1_tarski(sK6(sK4)),sK3)) ),
    inference(resolution,[],[f324,f88])).

fof(f351,plain,
    ( ~ v1_tdlat_3(sK5(k1_tarski(sK6(sK4)),sK3))
    | v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f328,f85])).

fof(f328,plain,(
    m1_pre_topc(sK5(k1_tarski(sK6(sK4)),sK3),sK3) ),
    inference(resolution,[],[f324,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:50:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (13119)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  % (13127)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (13116)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (13124)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (13128)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (13120)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13110)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (13107)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (13109)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (13107)Refutation not found, incomplete strategy% (13107)------------------------------
% 0.21/0.52  % (13107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13107)Memory used [KB]: 10618
% 0.21/0.52  % (13107)Time elapsed: 0.101 s
% 0.21/0.52  % (13107)------------------------------
% 0.21/0.52  % (13107)------------------------------
% 0.21/0.52  % (13114)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (13120)Refutation not found, incomplete strategy% (13120)------------------------------
% 0.21/0.52  % (13120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13120)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13120)Memory used [KB]: 6140
% 0.21/0.52  % (13120)Time elapsed: 0.060 s
% 0.21/0.52  % (13120)------------------------------
% 0.21/0.52  % (13120)------------------------------
% 0.21/0.52  % (13112)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (13111)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (13122)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (13115)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (13108)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (13126)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (13117)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (13132)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (13118)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (13123)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.55  % (13130)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (13115)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f770,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f743,f720])).
% 0.21/0.55  fof(f720,plain,(
% 0.21/0.55    v2_tex_2(sK4,sK3)),
% 0.21/0.55    inference(backward_demodulation,[],[f305,f711])).
% 0.21/0.55  fof(f711,plain,(
% 0.21/0.55    sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f710,f188])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ~v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.55    inference(subsumption_resolution,[],[f187,f78])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    sK4 = k1_tarski(sK6(sK4)) | ~v1_zfmisc_1(sK4) | v1_xboole_0(k1_tarski(sK6(sK4)))),
% 0.21/0.55    inference(subsumption_resolution,[],[f186,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ~v1_xboole_0(sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f48,f50,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.55    inference(negated_conjecture,[],[f18])).
% 0.21/0.55  fof(f18,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.55  fof(f186,plain,(
% 0.21/0.55    sK4 = k1_tarski(sK6(sK4)) | ~v1_zfmisc_1(sK4) | v1_xboole_0(sK4) | v1_xboole_0(k1_tarski(sK6(sK4)))),
% 0.21/0.55    inference(resolution,[],[f166,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,axiom,(
% 0.21/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    r1_tarski(k1_tarski(sK6(sK4)),sK4)),
% 0.21/0.55    inference(resolution,[],[f142,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    r2_hidden(sK6(sK4),sK4)),
% 0.21/0.56    inference(resolution,[],[f74,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f57,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(rectify,[],[f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.56  fof(f710,plain,(
% 0.21/0.56    v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f709,f374])).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    sP0(sK4,sK3) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f314,f155])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ~v2_tex_2(sK4,sK3) | sP0(sK4,sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f154,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ~v2_struct_0(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f153,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    v2_pre_topc(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f152,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    l1_pre_topc(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f148,f74])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    sP0(sK4,sK3) | ~v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f75,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP0(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (sP0(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(definition_folding,[],[f35,f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.56    inference(pure_predicate_removal,[],[f16])).
% 0.21/0.56  fof(f16,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f314,plain,(
% 0.21/0.56    v2_tex_2(sK4,sK3) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f311,f78])).
% 0.21/0.56  fof(f311,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | v2_tex_2(sK4,sK3) | v1_xboole_0(k1_tarski(sK6(sK4)))),
% 0.21/0.56    inference(resolution,[],[f177,f166])).
% 0.21/0.56  fof(f177,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,sK4) | sK4 = X0 | v2_tex_2(sK4,sK3) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f176,f74])).
% 0.21/0.56  fof(f176,plain,(
% 0.21/0.56    ( ! [X0] : (v2_tex_2(sK4,sK3) | sK4 = X0 | ~r1_tarski(X0,sK4) | v1_xboole_0(sK4) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(resolution,[],[f76,f79])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f709,plain,(
% 0.21/0.56    v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK6(sK4)) | ~sP0(sK4,sK3)),
% 0.21/0.56    inference(superposition,[],[f638,f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0,X1] : (u1_struct_0(sK5(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ! [X0,X1] : ((u1_struct_0(sK5(X0,X1)) = X0 & m1_pre_topc(sK5(X0,X1),X1) & v1_tdlat_3(sK5(X0,X1)) & ~v2_struct_0(sK5(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f53,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK5(X0,X1)) = X0 & m1_pre_topc(sK5(X0,X1),X1) & v1_tdlat_3(sK5(X0,X1)) & ~v2_struct_0(sK5(X0,X1))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP0(X0,X1))),
% 0.21/0.56    inference(rectify,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP0(X1,X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f42])).
% 0.21/0.56  fof(f638,plain,(
% 0.21/0.56    v1_zfmisc_1(u1_struct_0(sK5(sK4,sK3))) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f637,f539])).
% 0.21/0.56  fof(f539,plain,(
% 0.21/0.56    l1_struct_0(sK5(sK4,sK3)) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f432,f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.56  fof(f432,plain,(
% 0.21/0.56    l1_pre_topc(sK5(sK4,sK3)) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f374,f179])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X0] : (~sP0(X0,sK3) | l1_pre_topc(sK5(X0,sK3))) )),
% 0.21/0.56    inference(resolution,[],[f131,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_pre_topc(sK5(X0,X1),X1) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ( ! [X3] : (~m1_pre_topc(X3,sK3) | l1_pre_topc(X3)) )),
% 0.21/0.56    inference(resolution,[],[f73,f82])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.56  fof(f637,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | v1_zfmisc_1(u1_struct_0(sK5(sK4,sK3))) | ~l1_struct_0(sK5(sK4,sK3))),
% 0.21/0.56    inference(resolution,[],[f627,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.56  fof(f627,plain,(
% 0.21/0.56    v7_struct_0(sK5(sK4,sK3)) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f626,f433])).
% 0.21/0.56  fof(f433,plain,(
% 0.21/0.56    ~v2_struct_0(sK5(sK4,sK3)) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f374,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v2_struct_0(sK5(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f626,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3))),
% 0.21/0.56    inference(subsumption_resolution,[],[f625,f434])).
% 0.21/0.56  fof(f434,plain,(
% 0.21/0.56    v1_tdlat_3(sK5(sK4,sK3)) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f374,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_tdlat_3(sK5(X0,X1)) | ~sP0(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f625,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | ~v1_tdlat_3(sK5(sK4,sK3)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3))),
% 0.21/0.56    inference(subsumption_resolution,[],[f624,f70])).
% 0.21/0.56  fof(f624,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | ~v1_tdlat_3(sK5(sK4,sK3)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f623,f71])).
% 0.21/0.56  % (13131)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.56  fof(f623,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | ~v1_tdlat_3(sK5(sK4,sK3)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f622,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    v2_tdlat_3(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f622,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | ~v1_tdlat_3(sK5(sK4,sK3)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f620,f73])).
% 0.21/0.56  fof(f620,plain,(
% 0.21/0.56    sK4 = k1_tarski(sK6(sK4)) | ~v1_tdlat_3(sK5(sK4,sK3)) | v7_struct_0(sK5(sK4,sK3)) | v2_struct_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f435,f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v1_tdlat_3(X1) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.21/0.56  fof(f435,plain,(
% 0.21/0.56    m1_pre_topc(sK5(sK4,sK3),sK3) | sK4 = k1_tarski(sK6(sK4))),
% 0.21/0.56    inference(resolution,[],[f374,f89])).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    v2_tex_2(k1_tarski(sK6(sK4)),sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f304,f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(subsumption_resolution,[],[f150,f74])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    v1_xboole_0(sK4) | ~v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f75,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.56  fof(f304,plain,(
% 0.21/0.56    v2_tex_2(k1_tarski(sK6(sK4)),sK3) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(subsumption_resolution,[],[f300,f284])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    m1_subset_1(sK6(sK4),u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f278,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    r2_hidden(sK6(sK4),u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f268,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f68])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~r2_hidden(X1,X0) | ~r2_hidden(X1,X2)) & ((r2_hidden(X1,X0) & r2_hidden(X1,X2)) | ~sP1(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.56    inference(flattening,[],[f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ! [X1,X3,X0] : ((sP1(X1,X3,X0) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~sP1(X1,X3,X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X1,X3,X0] : (sP1(X1,X3,X0) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f268,plain,(
% 0.21/0.56    sP1(u1_struct_0(sK3),sK6(sK4),sK4)),
% 0.21/0.56    inference(resolution,[],[f205,f142])).
% 0.21/0.56  fof(f205,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(X0,sK4) | sP1(u1_struct_0(sK3),X0,sK4)) )),
% 0.21/0.56    inference(resolution,[],[f202,f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (sP1(X1,X4,X0) | ~r2_hidden(X4,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f63,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2))) => ((~sP1(X1,sK7(X0,X1,X2),X0) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (sP1(X1,sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~sP1(X1,X4,X0)) & (sP1(X1,X4,X0) | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : ((~sP1(X1,X3,X0) | ~r2_hidden(X3,X2)) & (sP1(X1,X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~sP1(X1,X3,X0)) & (sP1(X1,X3,X0) | ~r2_hidden(X3,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP2(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> sP1(X1,X3,X0)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    sP2(sK4,u1_struct_0(sK3),sK4)),
% 0.21/0.56    inference(superposition,[],[f111,f170])).
% 0.21/0.56  fof(f170,plain,(
% 0.21/0.56    sK4 = k3_xboole_0(sK4,u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f149,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.56  fof(f149,plain,(
% 0.21/0.56    r1_tarski(sK4,u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f75,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.56    inference(nnf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(X0,X1,k3_xboole_0(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP2(X0,X1,X2)) & (sP2(X0,X1,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP2(X0,X1,X2))),
% 0.21/0.56    inference(definition_folding,[],[f2,f45,f44])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.56  fof(f300,plain,(
% 0.21/0.56    v2_tex_2(k1_tarski(sK6(sK4)),sK3) | ~m1_subset_1(sK6(sK4),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(superposition,[],[f286,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK6(sK4)),sK3)),
% 0.21/0.56    inference(resolution,[],[f284,f137])).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f136,f70])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f129,f71])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ( ! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X1),sK3) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 0.21/0.56    inference(resolution,[],[f73,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,axiom,(
% 0.21/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.56  fof(f743,plain,(
% 0.21/0.56    ~v2_tex_2(sK4,sK3)),
% 0.21/0.56    inference(resolution,[],[f730,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f730,plain,(
% 0.21/0.56    v1_zfmisc_1(sK4)),
% 0.21/0.56    inference(backward_demodulation,[],[f369,f711])).
% 0.21/0.56  fof(f369,plain,(
% 0.21/0.56    v1_zfmisc_1(k1_tarski(sK6(sK4)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f368,f324])).
% 0.21/0.56  fof(f324,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f323,f70])).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f322,f71])).
% 0.21/0.56  fof(f322,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f321,f73])).
% 0.21/0.56  fof(f321,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f320,f78])).
% 0.21/0.56  fof(f320,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3) | v1_xboole_0(k1_tarski(sK6(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f316,f305])).
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    sP0(k1_tarski(sK6(sK4)),sK3) | ~v2_tex_2(k1_tarski(sK6(sK4)),sK3) | v1_xboole_0(k1_tarski(sK6(sK4))) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f294,f91])).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    m1_subset_1(k1_tarski(sK6(sK4)),k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.21/0.56    inference(resolution,[],[f283,f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f61])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    r1_tarski(k1_tarski(sK6(sK4)),u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f278,f99])).
% 0.21/0.56  fof(f368,plain,(
% 0.21/0.56    v1_zfmisc_1(k1_tarski(sK6(sK4))) | ~sP0(k1_tarski(sK6(sK4)),sK3)),
% 0.21/0.56    inference(superposition,[],[f365,f90])).
% 0.21/0.56  fof(f365,plain,(
% 0.21/0.56    v1_zfmisc_1(u1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)))),
% 0.21/0.56    inference(subsumption_resolution,[],[f364,f335])).
% 0.21/0.56  fof(f335,plain,(
% 0.21/0.56    l1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(resolution,[],[f325,f80])).
% 0.21/0.56  fof(f325,plain,(
% 0.21/0.56    l1_pre_topc(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(resolution,[],[f324,f179])).
% 0.21/0.56  fof(f364,plain,(
% 0.21/0.56    v1_zfmisc_1(u1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))) | ~l1_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(resolution,[],[f358,f92])).
% 0.21/0.56  fof(f358,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(subsumption_resolution,[],[f357,f70])).
% 0.21/0.56  fof(f357,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f356,f71])).
% 0.21/0.56  fof(f356,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f355,f72])).
% 0.21/0.56  fof(f355,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f354,f73])).
% 0.21/0.56  fof(f354,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f353,f326])).
% 0.21/0.56  fof(f326,plain,(
% 0.21/0.56    ~v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(resolution,[],[f324,f87])).
% 0.21/0.56  fof(f353,plain,(
% 0.21/0.56    v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(subsumption_resolution,[],[f351,f327])).
% 0.21/0.56  fof(f327,plain,(
% 0.21/0.56    v1_tdlat_3(sK5(k1_tarski(sK6(sK4)),sK3))),
% 0.21/0.56    inference(resolution,[],[f324,f88])).
% 0.21/0.56  fof(f351,plain,(
% 0.21/0.56    ~v1_tdlat_3(sK5(k1_tarski(sK6(sK4)),sK3)) | v7_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | v2_struct_0(sK5(k1_tarski(sK6(sK4)),sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f328,f85])).
% 0.21/0.56  fof(f328,plain,(
% 0.21/0.56    m1_pre_topc(sK5(k1_tarski(sK6(sK4)),sK3),sK3)),
% 0.21/0.56    inference(resolution,[],[f324,f89])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (13115)------------------------------
% 0.21/0.56  % (13115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (13115)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (13115)Memory used [KB]: 1918
% 0.21/0.56  % (13115)Time elapsed: 0.149 s
% 0.21/0.56  % (13115)------------------------------
% 0.21/0.56  % (13115)------------------------------
% 0.21/0.56  % (13113)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.45/0.56  % (13106)Success in time 0.2 s
%------------------------------------------------------------------------------
