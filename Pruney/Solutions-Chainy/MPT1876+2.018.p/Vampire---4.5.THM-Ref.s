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
% DateTime   : Thu Dec  3 13:21:38 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :  191 (16092 expanded)
%              Number of leaves         :   26 (4330 expanded)
%              Depth                    :   55
%              Number of atoms          :  696 (123196 expanded)
%              Number of equality atoms :   59 (2546 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1146,f986])).

fof(f986,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(backward_demodulation,[],[f701,f980])).

fof(f980,plain,(
    sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f979,f319])).

fof(f319,plain,
    ( ~ v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f318,f98])).

fof(f98,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f318,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(k1_tarski(sK7(sK4))) ),
    inference(subsumption_resolution,[],[f316,f94])).

fof(f94,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f67,f69,f68])).

fof(f68,plain,
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

fof(f69,plain,
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

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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

fof(f316,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | ~ v1_zfmisc_1(sK4)
    | v1_xboole_0(sK4)
    | v1_xboole_0(k1_tarski(sK7(sK4))) ),
    inference(resolution,[],[f236,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X0,X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f236,plain,(
    r1_tarski(k1_tarski(sK7(sK4)),sK4) ),
    inference(resolution,[],[f188,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f188,plain,(
    r2_hidden(sK7(sK4),sK4) ),
    inference(resolution,[],[f94,f123])).

fof(f123,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK7(X0),X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f81,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f80])).

fof(f80,plain,(
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

fof(f979,plain,
    ( v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f978,f450])).

fof(f450,plain,
    ( sP2(sK4,sK3)
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f397,f210])).

fof(f210,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | sP2(sK4,sK3) ),
    inference(subsumption_resolution,[],[f209,f90])).

fof(f90,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f209,plain,
    ( sP2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f208,f91])).

fof(f91,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f208,plain,
    ( sP2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f207,f93])).

fof(f93,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f207,plain,
    ( sP2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f198,f94])).

fof(f198,plain,
    ( sP2(sK4,sK3)
    | ~ v2_tex_2(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f95,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f48,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(pure_predicate_removal,[],[f22])).

fof(f22,axiom,(
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

fof(f95,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

fof(f397,plain,
    ( v2_tex_2(sK4,sK3)
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f319,f96])).

fof(f96,plain,
    ( v1_zfmisc_1(sK4)
    | v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f978,plain,
    ( v1_zfmisc_1(sK4)
    | sK4 = k1_tarski(sK7(sK4))
    | ~ sP2(sK4,sK3) ),
    inference(superposition,[],[f951,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK6(X0,X1)) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK6(X0,X1)) = X0
        & m1_pre_topc(sK6(X0,X1),X1)
        & v1_tdlat_3(sK6(X0,X1))
        & ~ v2_struct_0(sK6(X0,X1)) )
      | ~ sP2(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f77,f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK6(X0,X1)) = X0
        & m1_pre_topc(sK6(X0,X1),X1)
        & v1_tdlat_3(sK6(X0,X1))
        & ~ v2_struct_0(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f951,plain,
    ( v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3)))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f950,f522])).

fof(f522,plain,
    ( l1_struct_0(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f476,f101])).

fof(f101,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f476,plain,
    ( l1_pre_topc(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f450,f257])).

fof(f257,plain,(
    ! [X1] :
      ( ~ sP2(X1,sK3)
      | l1_pre_topc(sK6(X1,sK3)) ) ),
    inference(resolution,[],[f165,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK6(X0,X1),X1)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK3)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f93,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f950,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3)))
    | ~ l1_struct_0(sK6(sK4,sK3)) ),
    inference(resolution,[],[f947,f121])).

fof(f121,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f947,plain,
    ( v7_struct_0(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f941,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v7_struct_0(X0)
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f941,plain,
    ( sP0(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f940,f476])).

fof(f940,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | sP0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f939,f477])).

fof(f477,plain,
    ( ~ v2_struct_0(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f450,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK6(X0,X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f939,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | sP0(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f938,f478])).

fof(f478,plain,
    ( v1_tdlat_3(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f450,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK6(X0,X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f938,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | sP0(sK6(sK4,sK3))
    | ~ v1_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f930,f914])).

fof(f914,plain,
    ( v2_tdlat_3(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f913,f90])).

fof(f913,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v2_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f912,f91])).

fof(f912,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v2_tdlat_3(sK6(sK4,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f911,f92])).

fof(f92,plain,(
    v2_tdlat_3(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f911,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v2_tdlat_3(sK6(sK4,sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f908,f93])).

fof(f908,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v2_tdlat_3(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f479,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( v2_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f479,plain,
    ( m1_pre_topc(sK6(sK4,sK3),sK3)
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(resolution,[],[f450,f118])).

fof(f930,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | sP0(sK6(sK4,sK3))
    | ~ v2_tdlat_3(sK6(sK4,sK3))
    | ~ v1_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(resolution,[],[f926,f106])).

fof(f106,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f36,f60])).

fof(f36,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f926,plain,
    ( v2_pre_topc(sK6(sK4,sK3))
    | sK4 = k1_tarski(sK7(sK4)) ),
    inference(subsumption_resolution,[],[f920,f476])).

fof(f920,plain,
    ( sK4 = k1_tarski(sK7(sK4))
    | v2_pre_topc(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(resolution,[],[f914,f102])).

fof(f102,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f701,plain,(
    v2_tex_2(k1_tarski(sK7(sK4)),sK3) ),
    inference(subsumption_resolution,[],[f700,f217])).

fof(f217,plain,(
    ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f203,f94])).

fof(f203,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f95,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f700,plain,
    ( v2_tex_2(k1_tarski(sK7(sK4)),sK3)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f696,f646])).

fof(f646,plain,(
    m1_subset_1(sK7(sK4),u1_struct_0(sK3)) ),
    inference(resolution,[],[f642,f237])).

fof(f237,plain,(
    m1_subset_1(sK7(sK4),sK4) ),
    inference(resolution,[],[f188,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f642,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK4)
      | m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(forward_demodulation,[],[f275,f221])).

fof(f221,plain,(
    sK4 = u1_struct_0(sK5(sK4,sK3)) ),
    inference(resolution,[],[f213,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK5(X0,X1)) = X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( u1_struct_0(sK5(X0,X1)) = X0
        & m1_pre_topc(sK5(X0,X1),X1)
        & ~ v2_struct_0(sK5(X0,X1)) )
      | ~ sP1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f73,f74])).

fof(f74,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK5(X0,X1)) = X0
        & m1_pre_topc(sK5(X0,X1),X1)
        & ~ v2_struct_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X0
          & m1_pre_topc(X2,X1)
          & ~ v2_struct_0(X2) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f213,plain,(
    sP1(sK4,sK3) ),
    inference(subsumption_resolution,[],[f212,f90])).

fof(f212,plain,
    ( sP1(sK4,sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f211,f93])).

fof(f211,plain,
    ( sP1(sK4,sK3)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f199,plain,
    ( sP1(sK4,sK3)
    | v1_xboole_0(sK4)
    | ~ l1_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f95,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f42,f62])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

% (10487)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f275,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3))) ) ),
    inference(subsumption_resolution,[],[f274,f90])).

fof(f274,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3)))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f273,f93])).

fof(f273,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3)))
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f267,f219])).

fof(f219,plain,(
    ~ v2_struct_0(sK5(sK4,sK3)) ),
    inference(resolution,[],[f213,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK5(X0,X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f267,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3)))
      | v2_struct_0(sK5(sK4,sK3))
      | ~ l1_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f220,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f220,plain,(
    m1_pre_topc(sK5(sK4,sK3),sK3) ),
    inference(resolution,[],[f213,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK5(X0,X1),X1)
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f696,plain,
    ( v2_tex_2(k1_tarski(sK7(sK4)),sK3)
    | ~ m1_subset_1(sK7(sK4),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(superposition,[],[f650,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f650,plain,(
    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK7(sK4)),sK3) ),
    inference(resolution,[],[f646,f180])).

fof(f180,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK3))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3) ) ),
    inference(subsumption_resolution,[],[f179,f90])).

fof(f179,plain,(
    ! [X5] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | v2_struct_0(sK3) ) ),
    inference(subsumption_resolution,[],[f169,f91])).

fof(f169,plain,(
    ! [X5] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3)
      | ~ m1_subset_1(X5,u1_struct_0(sK3))
      | ~ v2_pre_topc(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f93,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(f1146,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(resolution,[],[f1143,f97])).

fof(f97,plain,
    ( ~ v1_zfmisc_1(sK4)
    | ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f1143,plain,(
    v1_zfmisc_1(sK4) ),
    inference(subsumption_resolution,[],[f1142,f1011])).

fof(f1011,plain,(
    sP2(sK4,sK3) ),
    inference(resolution,[],[f986,f210])).

fof(f1142,plain,
    ( v1_zfmisc_1(sK4)
    | ~ sP2(sK4,sK3) ),
    inference(superposition,[],[f1138,f119])).

fof(f1138,plain,(
    v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3))) ),
    inference(subsumption_resolution,[],[f1137,f1033])).

fof(f1033,plain,(
    l1_struct_0(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1018,f101])).

fof(f1018,plain,(
    l1_pre_topc(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1011,f257])).

fof(f1137,plain,
    ( v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3)))
    | ~ l1_struct_0(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1134,f121])).

fof(f1134,plain,(
    v7_struct_0(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1119,f104])).

fof(f1119,plain,(
    sP0(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1118,f1018])).

fof(f1118,plain,
    ( sP0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1117,f1019])).

fof(f1019,plain,(
    ~ v2_struct_0(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1011,f116])).

fof(f1117,plain,
    ( sP0(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1116,f1020])).

fof(f1020,plain,(
    v1_tdlat_3(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1011,f117])).

fof(f1116,plain,
    ( sP0(sK6(sK4,sK3))
    | ~ v1_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1108,f1092])).

fof(f1092,plain,(
    v2_tdlat_3(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1091,f90])).

fof(f1091,plain,
    ( v2_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1090,f91])).

fof(f1090,plain,
    ( v2_tdlat_3(sK6(sK4,sK3))
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1089,f92])).

fof(f1089,plain,
    ( v2_tdlat_3(sK6(sK4,sK3))
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f1086,f93])).

% (10495)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f1086,plain,
    ( v2_tdlat_3(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK3)
    | ~ v2_tdlat_3(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f1021,f114])).

fof(f1021,plain,(
    m1_pre_topc(sK6(sK4,sK3),sK3) ),
    inference(resolution,[],[f1011,f118])).

fof(f1108,plain,
    ( sP0(sK6(sK4,sK3))
    | ~ v2_tdlat_3(sK6(sK4,sK3))
    | ~ v1_tdlat_3(sK6(sK4,sK3))
    | v2_struct_0(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1104,f106])).

fof(f1104,plain,(
    v2_pre_topc(sK6(sK4,sK3)) ),
    inference(subsumption_resolution,[],[f1098,f1018])).

fof(f1098,plain,
    ( v2_pre_topc(sK6(sK4,sK3))
    | ~ l1_pre_topc(sK6(sK4,sK3)) ),
    inference(resolution,[],[f1092,f102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (10475)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (10473)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (10488)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.50  % (10479)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.50  % (10493)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (10483)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.50  % (10476)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (10474)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (10485)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.50  % (10476)Refutation not found, incomplete strategy% (10476)------------------------------
% 0.20/0.50  % (10476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (10476)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (10476)Memory used [KB]: 6140
% 0.20/0.50  % (10476)Time elapsed: 0.098 s
% 0.20/0.50  % (10476)------------------------------
% 0.20/0.50  % (10476)------------------------------
% 0.20/0.51  % (10489)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (10478)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (10472)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (10480)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (10477)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (10490)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (10486)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (10496)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.24/0.52  % (10471)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.24/0.52  % (10491)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.24/0.52  % (10481)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.24/0.52  % (10477)Refutation not found, incomplete strategy% (10477)------------------------------
% 1.24/0.52  % (10477)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (10482)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.24/0.52  % (10478)Refutation not found, incomplete strategy% (10478)------------------------------
% 1.24/0.52  % (10478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (10478)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (10477)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (10477)Memory used [KB]: 10746
% 1.24/0.52  % (10477)Time elapsed: 0.072 s
% 1.24/0.52  % (10477)------------------------------
% 1.24/0.52  % (10477)------------------------------
% 1.24/0.52  % (10478)Memory used [KB]: 1791
% 1.24/0.52  % (10478)Time elapsed: 0.104 s
% 1.24/0.52  % (10478)------------------------------
% 1.24/0.52  % (10478)------------------------------
% 1.24/0.52  % (10494)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.24/0.52  % (10472)Refutation not found, incomplete strategy% (10472)------------------------------
% 1.24/0.52  % (10472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (10472)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (10472)Memory used [KB]: 10746
% 1.24/0.52  % (10472)Time elapsed: 0.100 s
% 1.24/0.52  % (10472)------------------------------
% 1.24/0.52  % (10472)------------------------------
% 1.24/0.52  % (10471)Refutation not found, incomplete strategy% (10471)------------------------------
% 1.24/0.52  % (10471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (10471)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (10471)Memory used [KB]: 10618
% 1.24/0.52  % (10471)Time elapsed: 0.118 s
% 1.24/0.52  % (10471)------------------------------
% 1.24/0.52  % (10471)------------------------------
% 1.24/0.53  % (10492)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.24/0.53  % (10484)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.44/0.54  % (10484)Refutation not found, incomplete strategy% (10484)------------------------------
% 1.44/0.54  % (10484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (10484)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (10484)Memory used [KB]: 6268
% 1.44/0.54  % (10484)Time elapsed: 0.130 s
% 1.44/0.54  % (10484)------------------------------
% 1.44/0.54  % (10484)------------------------------
% 1.44/0.54  % (10479)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f1149,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(subsumption_resolution,[],[f1146,f986])).
% 1.44/0.54  fof(f986,plain,(
% 1.44/0.54    v2_tex_2(sK4,sK3)),
% 1.44/0.54    inference(backward_demodulation,[],[f701,f980])).
% 1.44/0.54  fof(f980,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f979,f319])).
% 1.44/0.54  fof(f319,plain,(
% 1.44/0.54    ~v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f318,f98])).
% 1.44/0.54  fof(f98,plain,(
% 1.44/0.54    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f3])).
% 1.44/0.54  fof(f3,axiom,(
% 1.44/0.54    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.44/0.54  fof(f318,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | ~v1_zfmisc_1(sK4) | v1_xboole_0(k1_tarski(sK7(sK4)))),
% 1.44/0.54    inference(subsumption_resolution,[],[f316,f94])).
% 1.44/0.54  fof(f94,plain,(
% 1.44/0.54    ~v1_xboole_0(sK4)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f70,plain,(
% 1.44/0.54    ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f67,f69,f68])).
% 1.44/0.54  fof(f68,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_tdlat_3(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f69,plain,(
% 1.44/0.54    ? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,sK3)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)) & (v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & ~v1_xboole_0(sK4))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f67,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f66])).
% 1.44/0.54  fof(f66,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v2_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/0.54    inference(nnf_transformation,[],[f29])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f25])).
% 1.44/0.54  fof(f25,negated_conjecture,(
% 1.44/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.44/0.54    inference(negated_conjecture,[],[f24])).
% 1.44/0.54  fof(f24,conjecture,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.44/0.54  fof(f316,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | ~v1_zfmisc_1(sK4) | v1_xboole_0(sK4) | v1_xboole_0(k1_tarski(sK7(sK4)))),
% 1.44/0.54    inference(resolution,[],[f236,f100])).
% 1.44/0.54  fof(f100,plain,(
% 1.44/0.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.44/0.54    inference(flattening,[],[f30])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f21])).
% 1.44/0.54  fof(f21,axiom,(
% 1.44/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.44/0.54  fof(f236,plain,(
% 1.44/0.54    r1_tarski(k1_tarski(sK7(sK4)),sK4)),
% 1.44/0.54    inference(resolution,[],[f188,f135])).
% 1.44/0.54  fof(f135,plain,(
% 1.44/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f89])).
% 1.44/0.54  fof(f89,plain,(
% 1.44/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.44/0.54    inference(nnf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.44/0.54  fof(f188,plain,(
% 1.44/0.54    r2_hidden(sK7(sK4),sK4)),
% 1.44/0.54    inference(resolution,[],[f94,f123])).
% 1.44/0.54  fof(f123,plain,(
% 1.44/0.54    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f83])).
% 1.44/0.54  fof(f83,plain,(
% 1.44/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f81,f82])).
% 1.44/0.54  fof(f82,plain,(
% 1.44/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f81,plain,(
% 1.44/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.54    inference(rectify,[],[f80])).
% 1.44/0.54  fof(f80,plain,(
% 1.44/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.44/0.54    inference(nnf_transformation,[],[f1])).
% 1.44/0.54  fof(f1,axiom,(
% 1.44/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.54  fof(f979,plain,(
% 1.44/0.54    v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f978,f450])).
% 1.44/0.54  fof(f450,plain,(
% 1.44/0.54    sP2(sK4,sK3) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f397,f210])).
% 1.44/0.54  fof(f210,plain,(
% 1.44/0.54    ~v2_tex_2(sK4,sK3) | sP2(sK4,sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f209,f90])).
% 1.44/0.54  fof(f90,plain,(
% 1.44/0.54    ~v2_struct_0(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f209,plain,(
% 1.44/0.54    sP2(sK4,sK3) | ~v2_tex_2(sK4,sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f208,f91])).
% 1.44/0.54  fof(f91,plain,(
% 1.44/0.54    v2_pre_topc(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f208,plain,(
% 1.44/0.54    sP2(sK4,sK3) | ~v2_tex_2(sK4,sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f207,f93])).
% 1.44/0.54  fof(f93,plain,(
% 1.44/0.54    l1_pre_topc(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f207,plain,(
% 1.44/0.54    sP2(sK4,sK3) | ~v2_tex_2(sK4,sK3) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f198,f94])).
% 1.44/0.54  fof(f198,plain,(
% 1.44/0.54    sP2(sK4,sK3) | ~v2_tex_2(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(resolution,[],[f95,f120])).
% 1.44/0.54  fof(f120,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f65])).
% 1.44/0.54  fof(f65,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (sP2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(definition_folding,[],[f48,f64])).
% 1.44/0.54  fof(f64,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP2(X1,X0))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.54  fof(f48,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f47])).
% 1.44/0.54  fof(f47,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f26])).
% 1.44/0.54  fof(f26,plain,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.44/0.54    inference(pure_predicate_removal,[],[f22])).
% 1.44/0.54  fof(f22,axiom,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tex_2)).
% 1.44/0.54  fof(f95,plain,(
% 1.44/0.54    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f397,plain,(
% 1.44/0.54    v2_tex_2(sK4,sK3) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f319,f96])).
% 1.44/0.54  fof(f96,plain,(
% 1.44/0.54    v1_zfmisc_1(sK4) | v2_tex_2(sK4,sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f978,plain,(
% 1.44/0.54    v1_zfmisc_1(sK4) | sK4 = k1_tarski(sK7(sK4)) | ~sP2(sK4,sK3)),
% 1.44/0.54    inference(superposition,[],[f951,f119])).
% 1.44/0.54  fof(f119,plain,(
% 1.44/0.54    ( ! [X0,X1] : (u1_struct_0(sK6(X0,X1)) = X0 | ~sP2(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f79])).
% 1.44/0.54  fof(f79,plain,(
% 1.44/0.54    ! [X0,X1] : ((u1_struct_0(sK6(X0,X1)) = X0 & m1_pre_topc(sK6(X0,X1),X1) & v1_tdlat_3(sK6(X0,X1)) & ~v2_struct_0(sK6(X0,X1))) | ~sP2(X0,X1))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f77,f78])).
% 1.44/0.54  fof(f78,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) => (u1_struct_0(sK6(X0,X1)) = X0 & m1_pre_topc(sK6(X0,X1),X1) & v1_tdlat_3(sK6(X0,X1)) & ~v2_struct_0(sK6(X0,X1))))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f77,plain,(
% 1.44/0.54    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP2(X0,X1))),
% 1.44/0.54    inference(rectify,[],[f76])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & ~v2_struct_0(X2)) | ~sP2(X1,X0))),
% 1.44/0.54    inference(nnf_transformation,[],[f64])).
% 1.44/0.54  fof(f951,plain,(
% 1.44/0.54    v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3))) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f950,f522])).
% 1.44/0.54  fof(f522,plain,(
% 1.44/0.54    l1_struct_0(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f476,f101])).
% 1.44/0.54  fof(f101,plain,(
% 1.44/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f12])).
% 1.44/0.54  fof(f12,axiom,(
% 1.44/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.44/0.54  fof(f476,plain,(
% 1.44/0.54    l1_pre_topc(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f450,f257])).
% 1.44/0.54  fof(f257,plain,(
% 1.44/0.54    ( ! [X1] : (~sP2(X1,sK3) | l1_pre_topc(sK6(X1,sK3))) )),
% 1.44/0.54    inference(resolution,[],[f165,f118])).
% 1.44/0.54  fof(f118,plain,(
% 1.44/0.54    ( ! [X0,X1] : (m1_pre_topc(sK6(X0,X1),X1) | ~sP2(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f79])).
% 1.44/0.54  fof(f165,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_pre_topc(X0,sK3) | l1_pre_topc(X0)) )),
% 1.44/0.54    inference(resolution,[],[f93,f107])).
% 1.44/0.54  fof(f107,plain,(
% 1.44/0.54    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f37])).
% 1.44/0.54  fof(f37,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f13])).
% 1.44/0.54  fof(f13,axiom,(
% 1.44/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.44/0.54  fof(f950,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3))) | ~l1_struct_0(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f947,f121])).
% 1.44/0.54  fof(f121,plain,(
% 1.44/0.54    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f50])).
% 1.44/0.54  fof(f50,plain,(
% 1.44/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f49])).
% 1.44/0.54  fof(f49,plain,(
% 1.44/0.54    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f14])).
% 1.44/0.54  fof(f14,axiom,(
% 1.44/0.54    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.44/0.54  fof(f947,plain,(
% 1.44/0.54    v7_struct_0(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f941,f104])).
% 1.44/0.54  fof(f104,plain,(
% 1.44/0.54    ( ! [X0] : (v7_struct_0(X0) | ~sP0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f71])).
% 1.44/0.54  fof(f71,plain,(
% 1.44/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.44/0.54    inference(nnf_transformation,[],[f60])).
% 1.44/0.54  fof(f60,plain,(
% 1.44/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.44/0.54  fof(f941,plain,(
% 1.44/0.54    sP0(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f940,f476])).
% 1.44/0.54  fof(f940,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | sP0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f939,f477])).
% 1.44/0.54  fof(f477,plain,(
% 1.44/0.54    ~v2_struct_0(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f450,f116])).
% 1.44/0.54  fof(f116,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v2_struct_0(sK6(X0,X1)) | ~sP2(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f79])).
% 1.44/0.54  fof(f939,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | sP0(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f938,f478])).
% 1.44/0.54  fof(f478,plain,(
% 1.44/0.54    v1_tdlat_3(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f450,f117])).
% 1.44/0.54  fof(f117,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v1_tdlat_3(sK6(X0,X1)) | ~sP2(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f79])).
% 1.44/0.54  fof(f938,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | sP0(sK6(sK4,sK3)) | ~v1_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f930,f914])).
% 1.44/0.54  fof(f914,plain,(
% 1.44/0.54    v2_tdlat_3(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f913,f90])).
% 1.44/0.54  fof(f913,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v2_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f912,f91])).
% 1.44/0.54  fof(f912,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v2_tdlat_3(sK6(sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f911,f92])).
% 1.44/0.54  fof(f92,plain,(
% 1.44/0.54    v2_tdlat_3(sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f911,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v2_tdlat_3(sK6(sK4,sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f908,f93])).
% 1.44/0.54  fof(f908,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v2_tdlat_3(sK6(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(resolution,[],[f479,f114])).
% 1.44/0.54  fof(f114,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f44])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f43])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f19])).
% 1.44/0.54  fof(f19,axiom,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.44/0.54  fof(f479,plain,(
% 1.44/0.54    m1_pre_topc(sK6(sK4,sK3),sK3) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(resolution,[],[f450,f118])).
% 1.44/0.54  fof(f930,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | sP0(sK6(sK4,sK3)) | ~v2_tdlat_3(sK6(sK4,sK3)) | ~v1_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f926,f106])).
% 1.44/0.54  fof(f106,plain,(
% 1.44/0.54    ( ! [X0] : (sP0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f61])).
% 1.44/0.54  fof(f61,plain,(
% 1.44/0.54    ! [X0] : (sP0(X0) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(definition_folding,[],[f36,f60])).
% 1.44/0.54  fof(f36,plain,(
% 1.44/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(flattening,[],[f35])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f18])).
% 1.44/0.54  fof(f18,axiom,(
% 1.44/0.54    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.44/0.54  fof(f926,plain,(
% 1.44/0.54    v2_pre_topc(sK6(sK4,sK3)) | sK4 = k1_tarski(sK7(sK4))),
% 1.44/0.54    inference(subsumption_resolution,[],[f920,f476])).
% 1.44/0.54  fof(f920,plain,(
% 1.44/0.54    sK4 = k1_tarski(sK7(sK4)) | v2_pre_topc(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f914,f102])).
% 1.44/0.54  fof(f102,plain,(
% 1.44/0.54    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(flattening,[],[f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f17])).
% 1.44/0.54  fof(f17,axiom,(
% 1.44/0.54    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.44/0.54  fof(f701,plain,(
% 1.44/0.54    v2_tex_2(k1_tarski(sK7(sK4)),sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f700,f217])).
% 1.44/0.54  fof(f217,plain,(
% 1.44/0.54    ~v1_xboole_0(u1_struct_0(sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f203,f94])).
% 1.44/0.54  fof(f203,plain,(
% 1.44/0.54    v1_xboole_0(sK4) | ~v1_xboole_0(u1_struct_0(sK3))),
% 1.44/0.54    inference(resolution,[],[f95,f108])).
% 1.44/0.54  fof(f108,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f38])).
% 1.44/0.54  fof(f38,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.44/0.54    inference(ennf_transformation,[],[f7])).
% 1.44/0.54  fof(f7,axiom,(
% 1.44/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.44/0.54  fof(f700,plain,(
% 1.44/0.54    v2_tex_2(k1_tarski(sK7(sK4)),sK3) | v1_xboole_0(u1_struct_0(sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f696,f646])).
% 1.44/0.54  fof(f646,plain,(
% 1.44/0.54    m1_subset_1(sK7(sK4),u1_struct_0(sK3))),
% 1.44/0.54    inference(resolution,[],[f642,f237])).
% 1.44/0.54  fof(f237,plain,(
% 1.44/0.54    m1_subset_1(sK7(sK4),sK4)),
% 1.44/0.54    inference(resolution,[],[f188,f125])).
% 1.44/0.54  fof(f125,plain,(
% 1.44/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f51])).
% 1.44/0.54  fof(f51,plain,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.44/0.54    inference(ennf_transformation,[],[f8])).
% 1.44/0.54  fof(f8,axiom,(
% 1.44/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.44/0.54  fof(f642,plain,(
% 1.44/0.54    ( ! [X0] : (~m1_subset_1(X0,sK4) | m1_subset_1(X0,u1_struct_0(sK3))) )),
% 1.44/0.54    inference(forward_demodulation,[],[f275,f221])).
% 1.44/0.54  fof(f221,plain,(
% 1.44/0.54    sK4 = u1_struct_0(sK5(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f213,f112])).
% 1.44/0.54  fof(f112,plain,(
% 1.44/0.54    ( ! [X0,X1] : (u1_struct_0(sK5(X0,X1)) = X0 | ~sP1(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f75])).
% 1.44/0.54  fof(f75,plain,(
% 1.44/0.54    ! [X0,X1] : ((u1_struct_0(sK5(X0,X1)) = X0 & m1_pre_topc(sK5(X0,X1),X1) & ~v2_struct_0(sK5(X0,X1))) | ~sP1(X0,X1))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f73,f74])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => (u1_struct_0(sK5(X0,X1)) = X0 & m1_pre_topc(sK5(X0,X1),X1) & ~v2_struct_0(sK5(X0,X1))))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f73,plain,(
% 1.44/0.54    ! [X0,X1] : (? [X2] : (u1_struct_0(X2) = X0 & m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) | ~sP1(X0,X1))),
% 1.44/0.54    inference(rectify,[],[f72])).
% 1.44/0.54  fof(f72,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~sP1(X1,X0))),
% 1.44/0.54    inference(nnf_transformation,[],[f62])).
% 1.44/0.54  fof(f62,plain,(
% 1.44/0.54    ! [X1,X0] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~sP1(X1,X0))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.54  fof(f213,plain,(
% 1.44/0.54    sP1(sK4,sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f212,f90])).
% 1.44/0.54  fof(f212,plain,(
% 1.44/0.54    sP1(sK4,sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f211,f93])).
% 1.44/0.54  fof(f211,plain,(
% 1.44/0.54    sP1(sK4,sK3) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f199,f94])).
% 1.44/0.54  fof(f199,plain,(
% 1.44/0.54    sP1(sK4,sK3) | v1_xboole_0(sK4) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(resolution,[],[f95,f113])).
% 1.44/0.54  fof(f113,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f63])).
% 1.44/0.54  fof(f63,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (sP1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(definition_folding,[],[f42,f62])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f27])).
% 1.44/0.54  % (10487)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.44/0.54  fof(f27,plain,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 1.44/0.54    inference(pure_predicate_removal,[],[f20])).
% 1.44/0.54  fof(f20,axiom,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.44/0.54  fof(f275,plain,(
% 1.44/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3)))) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f274,f90])).
% 1.44/0.54  fof(f274,plain,(
% 1.44/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3))) | v2_struct_0(sK3)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f273,f93])).
% 1.44/0.54  fof(f273,plain,(
% 1.44/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3))) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f267,f219])).
% 1.44/0.54  fof(f219,plain,(
% 1.44/0.54    ~v2_struct_0(sK5(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f213,f110])).
% 1.44/0.54  fof(f110,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~v2_struct_0(sK5(X0,X1)) | ~sP1(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f75])).
% 1.44/0.54  fof(f267,plain,(
% 1.44/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK5(sK4,sK3))) | v2_struct_0(sK5(sK4,sK3)) | ~l1_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.44/0.54    inference(resolution,[],[f220,f109])).
% 1.44/0.54  fof(f109,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f40])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f15])).
% 1.44/0.54  fof(f15,axiom,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.44/0.54  fof(f220,plain,(
% 1.44/0.54    m1_pre_topc(sK5(sK4,sK3),sK3)),
% 1.44/0.54    inference(resolution,[],[f213,f111])).
% 1.44/0.54  fof(f111,plain,(
% 1.44/0.54    ( ! [X0,X1] : (m1_pre_topc(sK5(X0,X1),X1) | ~sP1(X0,X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f75])).
% 1.44/0.54  fof(f696,plain,(
% 1.44/0.54    v2_tex_2(k1_tarski(sK7(sK4)),sK3) | ~m1_subset_1(sK7(sK4),u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))),
% 1.44/0.54    inference(superposition,[],[f650,f130])).
% 1.44/0.54  fof(f130,plain,(
% 1.44/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f59])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.44/0.54    inference(flattening,[],[f58])).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f16])).
% 1.44/0.54  fof(f16,axiom,(
% 1.44/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.44/0.54  fof(f650,plain,(
% 1.44/0.54    v2_tex_2(k6_domain_1(u1_struct_0(sK3),sK7(sK4)),sK3)),
% 1.44/0.54    inference(resolution,[],[f646,f180])).
% 1.44/0.54  fof(f180,plain,(
% 1.44/0.54    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK3)) | v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f179,f90])).
% 1.44/0.54  fof(f179,plain,(
% 1.44/0.54    ( ! [X5] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3) | ~m1_subset_1(X5,u1_struct_0(sK3)) | v2_struct_0(sK3)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f169,f91])).
% 1.44/0.54  fof(f169,plain,(
% 1.44/0.54    ( ! [X5] : (v2_tex_2(k6_domain_1(u1_struct_0(sK3),X5),sK3) | ~m1_subset_1(X5,u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) )),
% 1.44/0.54    inference(resolution,[],[f93,f115])).
% 1.44/0.54  fof(f115,plain,(
% 1.44/0.54    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f46])).
% 1.44/0.54  fof(f46,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f45])).
% 1.44/0.54  fof(f45,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f23])).
% 1.44/0.54  fof(f23,axiom,(
% 1.44/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).
% 1.44/0.54  fof(f1146,plain,(
% 1.44/0.54    ~v2_tex_2(sK4,sK3)),
% 1.44/0.54    inference(resolution,[],[f1143,f97])).
% 1.44/0.54  fof(f97,plain,(
% 1.44/0.54    ~v1_zfmisc_1(sK4) | ~v2_tex_2(sK4,sK3)),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f1143,plain,(
% 1.44/0.54    v1_zfmisc_1(sK4)),
% 1.44/0.54    inference(subsumption_resolution,[],[f1142,f1011])).
% 1.44/0.54  fof(f1011,plain,(
% 1.44/0.54    sP2(sK4,sK3)),
% 1.44/0.54    inference(resolution,[],[f986,f210])).
% 1.44/0.54  fof(f1142,plain,(
% 1.44/0.54    v1_zfmisc_1(sK4) | ~sP2(sK4,sK3)),
% 1.44/0.54    inference(superposition,[],[f1138,f119])).
% 1.44/0.54  fof(f1138,plain,(
% 1.44/0.54    v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3)))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1137,f1033])).
% 1.44/0.54  fof(f1033,plain,(
% 1.44/0.54    l1_struct_0(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1018,f101])).
% 1.44/0.54  fof(f1018,plain,(
% 1.44/0.54    l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1011,f257])).
% 1.44/0.54  fof(f1137,plain,(
% 1.44/0.54    v1_zfmisc_1(u1_struct_0(sK6(sK4,sK3))) | ~l1_struct_0(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1134,f121])).
% 1.44/0.54  fof(f1134,plain,(
% 1.44/0.54    v7_struct_0(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1119,f104])).
% 1.44/0.54  fof(f1119,plain,(
% 1.44/0.54    sP0(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1118,f1018])).
% 1.44/0.54  fof(f1118,plain,(
% 1.44/0.54    sP0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1117,f1019])).
% 1.44/0.54  fof(f1019,plain,(
% 1.44/0.54    ~v2_struct_0(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1011,f116])).
% 1.44/0.54  fof(f1117,plain,(
% 1.44/0.54    sP0(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1116,f1020])).
% 1.44/0.54  fof(f1020,plain,(
% 1.44/0.54    v1_tdlat_3(sK6(sK4,sK3))),
% 1.44/0.54    inference(resolution,[],[f1011,f117])).
% 1.44/0.54  fof(f1116,plain,(
% 1.44/0.54    sP0(sK6(sK4,sK3)) | ~v1_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1108,f1092])).
% 1.44/0.54  fof(f1092,plain,(
% 1.44/0.54    v2_tdlat_3(sK6(sK4,sK3))),
% 1.44/0.54    inference(subsumption_resolution,[],[f1091,f90])).
% 1.44/0.54  fof(f1091,plain,(
% 1.44/0.54    v2_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f1090,f91])).
% 1.44/0.54  fof(f1090,plain,(
% 1.44/0.54    v2_tdlat_3(sK6(sK4,sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f1089,f92])).
% 1.44/0.54  fof(f1089,plain,(
% 1.44/0.54    v2_tdlat_3(sK6(sK4,sK3)) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.54    inference(subsumption_resolution,[],[f1086,f93])).
% 1.44/0.55  % (10495)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.55  fof(f1086,plain,(
% 1.44/0.55    v2_tdlat_3(sK6(sK4,sK3)) | ~l1_pre_topc(sK3) | ~v2_tdlat_3(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)),
% 1.44/0.55    inference(resolution,[],[f1021,f114])).
% 1.44/0.55  fof(f1021,plain,(
% 1.44/0.55    m1_pre_topc(sK6(sK4,sK3),sK3)),
% 1.44/0.55    inference(resolution,[],[f1011,f118])).
% 1.44/0.55  fof(f1108,plain,(
% 1.44/0.55    sP0(sK6(sK4,sK3)) | ~v2_tdlat_3(sK6(sK4,sK3)) | ~v1_tdlat_3(sK6(sK4,sK3)) | v2_struct_0(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.55    inference(resolution,[],[f1104,f106])).
% 1.44/0.55  fof(f1104,plain,(
% 1.44/0.55    v2_pre_topc(sK6(sK4,sK3))),
% 1.44/0.55    inference(subsumption_resolution,[],[f1098,f1018])).
% 1.44/0.55  fof(f1098,plain,(
% 1.44/0.55    v2_pre_topc(sK6(sK4,sK3)) | ~l1_pre_topc(sK6(sK4,sK3))),
% 1.44/0.55    inference(resolution,[],[f1092,f102])).
% 1.44/0.55  % SZS output end Proof for theBenchmark
% 1.44/0.55  % (10479)------------------------------
% 1.44/0.55  % (10479)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (10479)Termination reason: Refutation
% 1.44/0.55  
% 1.44/0.55  % (10479)Memory used [KB]: 2046
% 1.44/0.55  % (10479)Time elapsed: 0.134 s
% 1.44/0.55  % (10479)------------------------------
% 1.44/0.55  % (10479)------------------------------
% 1.44/0.55  % (10470)Success in time 0.19 s
%------------------------------------------------------------------------------
