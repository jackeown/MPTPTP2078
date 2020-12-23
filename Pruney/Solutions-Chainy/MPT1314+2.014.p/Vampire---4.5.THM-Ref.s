%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:45 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 337 expanded)
%              Number of leaves         :   30 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  492 (1808 expanded)
%              Number of equality atoms :   54 ( 260 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f90,f125,f178,f187,f189,f230,f236,f313,f327,f329,f333,f341])).

fof(f341,plain,
    ( spl7_14
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | spl7_14
    | spl7_19 ),
    inference(resolution,[],[f246,f239])).

fof(f239,plain,
    ( sP0(k2_struct_0(sK3),sK4,sK4)
    | spl7_14 ),
    inference(resolution,[],[f217,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).

% (24141)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f217,plain,
    ( ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl7_14
  <=> r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f246,plain,
    ( ~ sP0(k2_struct_0(sK3),sK4,sK4)
    | spl7_19 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_19
  <=> sP0(k2_struct_0(sK3),sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f333,plain,(
    ~ spl7_17 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl7_17 ),
    inference(resolution,[],[f229,f44])).

fof(f44,plain,(
    ~ v3_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ v3_pre_topc(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v3_pre_topc(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK1)
              & m1_pre_topc(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(X1,sK1)
            & m1_pre_topc(X2,sK1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & sK2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(sK2,sK1)
          & m1_pre_topc(X2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v3_pre_topc(X3,X2)
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v3_pre_topc(sK2,sK1)
        & m1_pre_topc(X2,sK1) )
   => ( ? [X3] :
          ( ~ v3_pre_topc(X3,sK3)
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
      & v3_pre_topc(sK2,sK1)
      & m1_pre_topc(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( ~ v3_pre_topc(X3,sK3)
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ~ v3_pre_topc(sK4,sK3)
      & sK2 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f229,plain,
    ( v3_pre_topc(sK4,sK3)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl7_17
  <=> v3_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f329,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl7_20 ),
    inference(resolution,[],[f326,f65])).

fof(f65,plain,(
    v3_pre_topc(sK4,sK1) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f43,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f326,plain,
    ( ~ v3_pre_topc(sK4,sK1)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl7_20
  <=> v3_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f327,plain,
    ( ~ spl7_20
    | ~ spl7_3
    | spl7_17
    | ~ spl7_16
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f320,f245,f185,f223,f227,f112,f324])).

fof(f112,plain,
    ( spl7_3
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

% (24141)Refutation not found, incomplete strategy% (24141)------------------------------
% (24141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24141)Termination reason: Refutation not found, incomplete strategy

% (24141)Memory used [KB]: 10746
% (24141)Time elapsed: 0.128 s
% (24141)------------------------------
% (24141)------------------------------
fof(f223,plain,
    ( spl7_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f185,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3)))
        | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f320,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3)))
    | v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ v3_pre_topc(sK4,sK1)
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(superposition,[],[f186,f317])).

fof(f317,plain,
    ( sK4 = k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3)))
    | ~ spl7_19 ),
    inference(resolution,[],[f247,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f64,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ sP0(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f247,plain,
    ( sP0(k2_struct_0(sK3),sK4,sK4)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f245])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3)))
        | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f313,plain,
    ( ~ spl7_2
    | ~ spl7_14
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_14
    | spl7_15 ),
    inference(resolution,[],[f295,f216])).

fof(f216,plain,
    ( r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f215])).

fof(f295,plain,
    ( ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4)
    | ~ spl7_2
    | spl7_15 ),
    inference(resolution,[],[f265,f91])).

fof(f91,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f42,f86])).

fof(f86,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_2
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f42,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f27])).

fof(f265,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),X6) )
    | spl7_15 ),
    inference(resolution,[],[f221,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f221,plain,
    ( ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl7_15
  <=> r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f236,plain,
    ( ~ spl7_2
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl7_2
    | spl7_16 ),
    inference(resolution,[],[f225,f91])).

fof(f225,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f223])).

fof(f230,plain,
    ( ~ spl7_14
    | ~ spl7_15
    | ~ spl7_16
    | ~ spl7_3
    | spl7_17
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f212,f185,f227,f112,f223,f219,f215])).

fof(f212,plain,
    ( v3_pre_topc(sK4,sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3)))
    | ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3))
    | ~ r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4)
    | ~ spl7_13 ),
    inference(resolution,[],[f209,f65])).

fof(f209,plain,
    ( ! [X6] :
        ( ~ v3_pre_topc(X6,sK1)
        | v3_pre_topc(X6,sK3)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ r2_hidden(sK6(k2_struct_0(sK3),X6,X6),k2_struct_0(sK3))
        | ~ r2_hidden(sK6(k2_struct_0(sK3),X6,X6),X6) )
    | ~ spl7_13 ),
    inference(superposition,[],[f186,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK6(X0,X1,X1),X0)
      | ~ r2_hidden(sK6(X0,X1,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X1),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1
      | ~ r2_hidden(sK6(X0,X1,X1),X1)
      | k1_setfam_1(k2_tarski(X1,X0)) = X1 ) ),
    inference(resolution,[],[f194,f68])).

fof(f194,plain,(
    ! [X6,X7] :
      ( sP0(X6,X7,X7)
      | ~ r2_hidden(sK6(X6,X7,X7),X6)
      | k1_setfam_1(k2_tarski(X7,X6)) = X7
      | ~ r2_hidden(sK6(X6,X7,X7),X7) ) ),
    inference(resolution,[],[f152,f94])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | k1_setfam_1(k2_tarski(X1,X0)) = X2 ) ),
    inference(resolution,[],[f62,f68])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f189,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl7_12 ),
    inference(resolution,[],[f183,f72])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f46,f45])).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f183,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_12
  <=> m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f187,plain,
    ( ~ spl7_12
    | spl7_13
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f179,f176,f185,f181])).

fof(f176,plain,
    ( spl7_11
  <=> ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3)
        | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) )
    | ~ spl7_11 ),
    inference(superposition,[],[f177,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f54])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f177,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( ~ spl7_1
    | spl7_11
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f174,f84,f176,f80])).

fof(f80,plain,
    ( spl7_1
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f174,plain,
    ( ! [X0] :
        ( v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | ~ l1_pre_topc(sK1) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f173,f86])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
        | ~ v3_pre_topc(X0,sK1)
        | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
        | ~ l1_pre_topc(sK1) )
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f172,f86])).

fof(f172,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1)))
      | ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
      | ~ l1_pre_topc(sK1) ) ),
    inference(forward_demodulation,[],[f171,f74])).

fof(f74,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f73,f38])).

fof(f38,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(resolution,[],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f171,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)
      | ~ l1_pre_topc(sK1) ) ),
    inference(resolution,[],[f70,f40])).

fof(f40,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).

fof(f125,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f66,f74])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1)))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f112])).

fof(f90,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl7_1 ),
    inference(resolution,[],[f82,f38])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f87,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f78,f84,f80])).

fof(f78,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f75,f40])).

% (24156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (714932224)
% 0.13/0.37  ipcrm: permission denied for id (714997763)
% 0.13/0.37  ipcrm: permission denied for id (718897156)
% 0.13/0.37  ipcrm: permission denied for id (715161608)
% 0.13/0.37  ipcrm: permission denied for id (715227146)
% 0.13/0.37  ipcrm: permission denied for id (719061003)
% 0.13/0.38  ipcrm: permission denied for id (715325453)
% 0.13/0.38  ipcrm: permission denied for id (719126542)
% 0.13/0.38  ipcrm: permission denied for id (715390991)
% 0.13/0.38  ipcrm: permission denied for id (719159312)
% 0.13/0.38  ipcrm: permission denied for id (715456529)
% 0.13/0.38  ipcrm: permission denied for id (715489298)
% 0.13/0.38  ipcrm: permission denied for id (715522067)
% 0.13/0.39  ipcrm: permission denied for id (715554836)
% 0.13/0.39  ipcrm: permission denied for id (715587605)
% 0.13/0.39  ipcrm: permission denied for id (715620374)
% 0.13/0.39  ipcrm: permission denied for id (719192087)
% 0.13/0.39  ipcrm: permission denied for id (715685912)
% 0.13/0.39  ipcrm: permission denied for id (719224857)
% 0.20/0.39  ipcrm: permission denied for id (719257626)
% 0.20/0.39  ipcrm: permission denied for id (719290395)
% 0.20/0.39  ipcrm: permission denied for id (719323164)
% 0.20/0.40  ipcrm: permission denied for id (719355933)
% 0.20/0.40  ipcrm: permission denied for id (715915298)
% 0.20/0.40  ipcrm: permission denied for id (715980836)
% 0.20/0.41  ipcrm: permission denied for id (719683625)
% 0.20/0.41  ipcrm: permission denied for id (719716394)
% 0.20/0.41  ipcrm: permission denied for id (719749163)
% 0.20/0.41  ipcrm: permission denied for id (716242988)
% 0.20/0.41  ipcrm: permission denied for id (716275757)
% 0.20/0.42  ipcrm: permission denied for id (716308526)
% 0.20/0.42  ipcrm: permission denied for id (716341295)
% 0.20/0.42  ipcrm: permission denied for id (716374064)
% 0.20/0.42  ipcrm: permission denied for id (716406833)
% 0.20/0.42  ipcrm: permission denied for id (716439602)
% 0.20/0.42  ipcrm: permission denied for id (716472371)
% 0.20/0.42  ipcrm: permission denied for id (716505140)
% 0.20/0.43  ipcrm: permission denied for id (719847479)
% 0.20/0.43  ipcrm: permission denied for id (719880248)
% 0.20/0.43  ipcrm: permission denied for id (716668985)
% 0.20/0.43  ipcrm: permission denied for id (716701754)
% 0.20/0.43  ipcrm: permission denied for id (719913019)
% 0.20/0.43  ipcrm: permission denied for id (716767292)
% 0.20/0.43  ipcrm: permission denied for id (719945789)
% 0.20/0.43  ipcrm: permission denied for id (716832830)
% 0.20/0.44  ipcrm: permission denied for id (719978559)
% 0.20/0.44  ipcrm: permission denied for id (720011328)
% 0.20/0.44  ipcrm: permission denied for id (720175173)
% 0.20/0.44  ipcrm: permission denied for id (720207942)
% 0.20/0.44  ipcrm: permission denied for id (720240711)
% 0.20/0.45  ipcrm: permission denied for id (720273480)
% 0.20/0.45  ipcrm: permission denied for id (720306249)
% 0.20/0.45  ipcrm: permission denied for id (720339018)
% 0.20/0.45  ipcrm: permission denied for id (720371787)
% 0.20/0.45  ipcrm: permission denied for id (717193292)
% 0.20/0.45  ipcrm: permission denied for id (717258830)
% 0.20/0.45  ipcrm: permission denied for id (720437327)
% 0.20/0.46  ipcrm: permission denied for id (720470096)
% 0.20/0.46  ipcrm: permission denied for id (720502865)
% 0.20/0.46  ipcrm: permission denied for id (717389906)
% 0.20/0.46  ipcrm: permission denied for id (717422675)
% 0.20/0.46  ipcrm: permission denied for id (717455444)
% 0.20/0.46  ipcrm: permission denied for id (717488213)
% 0.20/0.46  ipcrm: permission denied for id (717520982)
% 0.20/0.46  ipcrm: permission denied for id (720535639)
% 0.20/0.46  ipcrm: permission denied for id (717553752)
% 0.20/0.47  ipcrm: permission denied for id (717586521)
% 0.20/0.47  ipcrm: permission denied for id (717619290)
% 0.20/0.47  ipcrm: permission denied for id (717652059)
% 0.20/0.47  ipcrm: permission denied for id (720568412)
% 0.20/0.47  ipcrm: permission denied for id (717750366)
% 0.20/0.47  ipcrm: permission denied for id (717815904)
% 0.20/0.48  ipcrm: permission denied for id (717946980)
% 0.20/0.48  ipcrm: permission denied for id (718045287)
% 0.20/0.48  ipcrm: permission denied for id (718078056)
% 0.20/0.48  ipcrm: permission denied for id (718110825)
% 0.20/0.49  ipcrm: permission denied for id (718143594)
% 0.20/0.49  ipcrm: permission denied for id (718209132)
% 0.20/0.49  ipcrm: permission denied for id (718274670)
% 0.20/0.49  ipcrm: permission denied for id (718340208)
% 0.20/0.50  ipcrm: permission denied for id (718405746)
% 0.20/0.50  ipcrm: permission denied for id (718471284)
% 0.20/0.50  ipcrm: permission denied for id (720994421)
% 0.20/0.50  ipcrm: permission denied for id (718536822)
% 0.20/0.50  ipcrm: permission denied for id (718602360)
% 0.20/0.50  ipcrm: permission denied for id (721059961)
% 0.20/0.51  ipcrm: permission denied for id (721158268)
% 0.20/0.51  ipcrm: permission denied for id (718798975)
% 0.36/0.63  % (24133)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.36/0.64  % (24139)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.36/0.64  % (24133)Refutation not found, incomplete strategy% (24133)------------------------------
% 0.36/0.64  % (24133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.65  % (24154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.36/0.65  % (24153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.36/0.65  % (24144)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.36/0.65  % (24148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.36/0.66  % (24134)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.36/0.66  % (24148)Refutation not found, incomplete strategy% (24148)------------------------------
% 0.36/0.66  % (24148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (24148)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (24148)Memory used [KB]: 10618
% 0.36/0.66  % (24148)Time elapsed: 0.111 s
% 0.36/0.66  % (24148)------------------------------
% 0.36/0.66  % (24148)------------------------------
% 0.36/0.66  % (24133)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (24133)Memory used [KB]: 10746
% 0.36/0.66  % (24133)Time elapsed: 0.093 s
% 0.36/0.66  % (24133)------------------------------
% 0.36/0.66  % (24133)------------------------------
% 0.36/0.66  % (24151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.36/0.66  % (24143)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.36/0.66  % (24136)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.36/0.66  % (24132)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.36/0.66  % (24139)Refutation not found, incomplete strategy% (24139)------------------------------
% 0.36/0.66  % (24139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (24139)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (24139)Memory used [KB]: 10746
% 0.36/0.66  % (24139)Time elapsed: 0.115 s
% 0.36/0.66  % (24139)------------------------------
% 0.36/0.66  % (24139)------------------------------
% 0.36/0.66  % (24142)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.36/0.66  % (24153)Refutation not found, incomplete strategy% (24153)------------------------------
% 0.36/0.66  % (24153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.66  % (24159)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.36/0.66  % (24153)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.66  
% 0.36/0.66  % (24153)Memory used [KB]: 10746
% 0.36/0.66  % (24153)Time elapsed: 0.119 s
% 0.36/0.66  % (24153)------------------------------
% 0.36/0.66  % (24153)------------------------------
% 0.36/0.67  % (24131)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.36/0.67  % (24158)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.36/0.67  % (24152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.36/0.67  % (24155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.36/0.67  % (24146)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.36/0.67  % (24138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.36/0.68  % (24140)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.36/0.68  % (24147)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.36/0.68  % (24137)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.36/0.68  % (24151)Refutation not found, incomplete strategy% (24151)------------------------------
% 0.36/0.68  % (24151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.68  % (24151)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.68  
% 0.36/0.68  % (24151)Memory used [KB]: 10746
% 0.36/0.68  % (24151)Time elapsed: 0.127 s
% 0.36/0.68  % (24151)------------------------------
% 0.36/0.68  % (24151)------------------------------
% 0.36/0.68  % (24145)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.36/0.69  % (24135)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.36/0.69  % (24152)Refutation not found, incomplete strategy% (24152)------------------------------
% 0.36/0.69  % (24152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.69  % (24152)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.69  
% 0.36/0.69  % (24152)Memory used [KB]: 1791
% 0.36/0.69  % (24152)Time elapsed: 0.117 s
% 0.36/0.69  % (24152)------------------------------
% 0.36/0.69  % (24152)------------------------------
% 0.36/0.69  % (24149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.36/0.69  % (24143)Refutation found. Thanks to Tanya!
% 0.36/0.69  % SZS status Theorem for theBenchmark
% 0.36/0.69  % SZS output start Proof for theBenchmark
% 0.36/0.69  fof(f342,plain,(
% 0.36/0.69    $false),
% 0.36/0.69    inference(avatar_sat_refutation,[],[f87,f90,f125,f178,f187,f189,f230,f236,f313,f327,f329,f333,f341])).
% 0.36/0.69  fof(f341,plain,(
% 0.36/0.69    spl7_14 | spl7_19),
% 0.36/0.69    inference(avatar_contradiction_clause,[],[f337])).
% 0.36/0.69  fof(f337,plain,(
% 0.36/0.69    $false | (spl7_14 | spl7_19)),
% 0.36/0.69    inference(resolution,[],[f246,f239])).
% 0.36/0.69  fof(f239,plain,(
% 0.36/0.69    sP0(k2_struct_0(sK3),sK4,sK4) | spl7_14),
% 0.36/0.69    inference(resolution,[],[f217,f94])).
% 0.36/0.69  fof(f94,plain,(
% 0.36/0.69    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 0.36/0.69    inference(factoring,[],[f60])).
% 0.36/0.69  fof(f60,plain,(
% 0.36/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 0.36/0.69    inference(cnf_transformation,[],[f36])).
% 0.36/0.69  fof(f36,plain,(
% 0.36/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.36/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f34,f35])).
% 0.36/0.69  % (24141)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.36/0.69  fof(f35,plain,(
% 0.36/0.69    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.36/0.69    introduced(choice_axiom,[])).
% 0.36/0.69  fof(f34,plain,(
% 0.36/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.36/0.69    inference(rectify,[],[f33])).
% 0.36/0.69  fof(f33,plain,(
% 0.36/0.69    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.36/0.69    inference(flattening,[],[f32])).
% 0.36/0.69  fof(f32,plain,(
% 0.36/0.69    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.36/0.69    inference(nnf_transformation,[],[f21])).
% 0.36/0.69  fof(f21,plain,(
% 0.36/0.69    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.36/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.36/0.69  fof(f217,plain,(
% 0.36/0.69    ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4) | spl7_14),
% 0.36/0.69    inference(avatar_component_clause,[],[f215])).
% 0.36/0.69  fof(f215,plain,(
% 0.36/0.69    spl7_14 <=> r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4)),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.36/0.69  fof(f246,plain,(
% 0.36/0.69    ~sP0(k2_struct_0(sK3),sK4,sK4) | spl7_19),
% 0.36/0.69    inference(avatar_component_clause,[],[f245])).
% 0.36/0.69  fof(f245,plain,(
% 0.36/0.69    spl7_19 <=> sP0(k2_struct_0(sK3),sK4,sK4)),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.36/0.69  fof(f333,plain,(
% 0.36/0.69    ~spl7_17),
% 0.36/0.69    inference(avatar_contradiction_clause,[],[f330])).
% 0.36/0.69  fof(f330,plain,(
% 0.36/0.69    $false | ~spl7_17),
% 0.36/0.69    inference(resolution,[],[f229,f44])).
% 0.36/0.69  fof(f44,plain,(
% 0.36/0.69    ~v3_pre_topc(sK4,sK3)),
% 0.36/0.69    inference(cnf_transformation,[],[f27])).
% 0.36/0.69  fof(f27,plain,(
% 0.36/0.69    (((~v3_pre_topc(sK4,sK3) & sK2 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(sK3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 0.36/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f26,f25,f24,f23])).
% 0.36/0.69  fof(f23,plain,(
% 0.36/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 0.36/0.69    introduced(choice_axiom,[])).
% 0.36/0.69  fof(f24,plain,(
% 0.36/0.69    ? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(X2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.36/0.69    introduced(choice_axiom,[])).
% 0.36/0.69  fof(f25,plain,(
% 0.36/0.69    ? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(X2,sK1)) => (? [X3] : (~v3_pre_topc(X3,sK3) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) & v3_pre_topc(sK2,sK1) & m1_pre_topc(sK3,sK1))),
% 0.36/0.69    introduced(choice_axiom,[])).
% 0.36/0.69  fof(f26,plain,(
% 0.36/0.69    ? [X3] : (~v3_pre_topc(X3,sK3) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3)))) => (~v3_pre_topc(sK4,sK3) & sK2 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))))),
% 0.36/0.69    introduced(choice_axiom,[])).
% 0.36/0.69  fof(f14,plain,(
% 0.36/0.69    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.36/0.69    inference(flattening,[],[f13])).
% 0.36/0.69  fof(f13,plain,(
% 0.36/0.69    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.36/0.69    inference(ennf_transformation,[],[f12])).
% 0.36/0.69  fof(f12,negated_conjecture,(
% 0.36/0.69    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.36/0.69    inference(negated_conjecture,[],[f11])).
% 0.36/0.69  fof(f11,conjecture,(
% 0.36/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.36/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.36/0.69  fof(f229,plain,(
% 0.36/0.69    v3_pre_topc(sK4,sK3) | ~spl7_17),
% 0.36/0.69    inference(avatar_component_clause,[],[f227])).
% 0.36/0.69  fof(f227,plain,(
% 0.36/0.69    spl7_17 <=> v3_pre_topc(sK4,sK3)),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.36/0.69  fof(f329,plain,(
% 0.36/0.69    spl7_20),
% 0.36/0.69    inference(avatar_contradiction_clause,[],[f328])).
% 0.36/0.69  fof(f328,plain,(
% 0.36/0.69    $false | spl7_20),
% 0.36/0.69    inference(resolution,[],[f326,f65])).
% 0.36/0.69  fof(f65,plain,(
% 0.36/0.69    v3_pre_topc(sK4,sK1)),
% 0.36/0.69    inference(definition_unfolding,[],[f41,f43])).
% 0.36/0.69  fof(f43,plain,(
% 0.36/0.69    sK2 = sK4),
% 0.36/0.69    inference(cnf_transformation,[],[f27])).
% 0.36/0.69  fof(f41,plain,(
% 0.36/0.69    v3_pre_topc(sK2,sK1)),
% 0.36/0.69    inference(cnf_transformation,[],[f27])).
% 0.36/0.69  fof(f326,plain,(
% 0.36/0.69    ~v3_pre_topc(sK4,sK1) | spl7_20),
% 0.36/0.69    inference(avatar_component_clause,[],[f324])).
% 0.36/0.69  fof(f324,plain,(
% 0.36/0.69    spl7_20 <=> v3_pre_topc(sK4,sK1)),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.36/0.69  fof(f327,plain,(
% 0.36/0.69    ~spl7_20 | ~spl7_3 | spl7_17 | ~spl7_16 | ~spl7_13 | ~spl7_19),
% 0.36/0.69    inference(avatar_split_clause,[],[f320,f245,f185,f223,f227,f112,f324])).
% 0.36/0.69  fof(f112,plain,(
% 0.36/0.69    spl7_3 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.36/0.69  % (24141)Refutation not found, incomplete strategy% (24141)------------------------------
% 0.36/0.69  % (24141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.69  % (24141)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.69  
% 0.36/0.69  % (24141)Memory used [KB]: 10746
% 0.36/0.69  % (24141)Time elapsed: 0.128 s
% 0.36/0.69  % (24141)------------------------------
% 0.36/0.69  % (24141)------------------------------
% 0.36/0.69  fof(f223,plain,(
% 0.36/0.69    spl7_16 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3)))),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.36/0.69  fof(f185,plain,(
% 0.36/0.69    spl7_13 <=> ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3))) | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1))),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.36/0.69  fof(f320,plain,(
% 0.36/0.69    ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) | v3_pre_topc(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(sK4,sK1) | (~spl7_13 | ~spl7_19)),
% 0.36/0.69    inference(superposition,[],[f186,f317])).
% 0.36/0.69  fof(f317,plain,(
% 0.36/0.69    sK4 = k1_setfam_1(k2_tarski(sK4,k2_struct_0(sK3))) | ~spl7_19),
% 0.36/0.69    inference(resolution,[],[f247,f68])).
% 0.36/0.69  fof(f68,plain,(
% 0.36/0.69    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 0.36/0.69    inference(definition_unfolding,[],[f64,f54])).
% 0.36/0.69  fof(f54,plain,(
% 0.36/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.36/0.69    inference(cnf_transformation,[],[f6])).
% 0.36/0.69  fof(f6,axiom,(
% 0.36/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.36/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.36/0.69  fof(f64,plain,(
% 0.36/0.69    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) )),
% 0.36/0.69    inference(cnf_transformation,[],[f37])).
% 0.36/0.69  fof(f37,plain,(
% 0.36/0.69    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 0.36/0.69    inference(nnf_transformation,[],[f22])).
% 0.36/0.69  fof(f22,plain,(
% 0.36/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.36/0.69    inference(definition_folding,[],[f1,f21])).
% 0.36/0.69  fof(f1,axiom,(
% 0.36/0.69    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.36/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.36/0.69  fof(f247,plain,(
% 0.36/0.69    sP0(k2_struct_0(sK3),sK4,sK4) | ~spl7_19),
% 0.36/0.69    inference(avatar_component_clause,[],[f245])).
% 0.36/0.69  fof(f186,plain,(
% 0.36/0.69    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3))) | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1)) ) | ~spl7_13),
% 0.36/0.69    inference(avatar_component_clause,[],[f185])).
% 0.36/0.69  fof(f313,plain,(
% 0.36/0.69    ~spl7_2 | ~spl7_14 | spl7_15),
% 0.36/0.69    inference(avatar_contradiction_clause,[],[f305])).
% 0.36/0.69  fof(f305,plain,(
% 0.36/0.69    $false | (~spl7_2 | ~spl7_14 | spl7_15)),
% 0.36/0.69    inference(resolution,[],[f295,f216])).
% 0.36/0.69  fof(f216,plain,(
% 0.36/0.69    r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4) | ~spl7_14),
% 0.36/0.69    inference(avatar_component_clause,[],[f215])).
% 0.36/0.69  fof(f295,plain,(
% 0.36/0.69    ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4) | (~spl7_2 | spl7_15)),
% 0.36/0.69    inference(resolution,[],[f265,f91])).
% 0.36/0.69  fof(f91,plain,(
% 0.36/0.69    m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) | ~spl7_2),
% 0.36/0.69    inference(backward_demodulation,[],[f42,f86])).
% 0.36/0.69  fof(f86,plain,(
% 0.36/0.69    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl7_2),
% 0.36/0.69    inference(avatar_component_clause,[],[f84])).
% 0.36/0.69  fof(f84,plain,(
% 0.36/0.69    spl7_2 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.36/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.61/0.69  fof(f42,plain,(
% 0.61/0.69    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 0.61/0.69    inference(cnf_transformation,[],[f27])).
% 0.61/0.69  fof(f265,plain,(
% 0.61/0.69    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK3))) | ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),X6)) ) | spl7_15),
% 0.61/0.69    inference(resolution,[],[f221,f55])).
% 0.61/0.69  fof(f55,plain,(
% 0.61/0.69    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.61/0.69    inference(cnf_transformation,[],[f19])).
% 0.61/0.69  fof(f19,plain,(
% 0.61/0.69    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.61/0.69    inference(ennf_transformation,[],[f4])).
% 0.61/0.69  fof(f4,axiom,(
% 0.61/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.61/0.69  fof(f221,plain,(
% 0.61/0.69    ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3)) | spl7_15),
% 0.61/0.69    inference(avatar_component_clause,[],[f219])).
% 0.61/0.69  fof(f219,plain,(
% 0.61/0.69    spl7_15 <=> r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3))),
% 0.61/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.61/0.69  fof(f236,plain,(
% 0.61/0.69    ~spl7_2 | spl7_16),
% 0.61/0.69    inference(avatar_contradiction_clause,[],[f235])).
% 0.61/0.69  fof(f235,plain,(
% 0.61/0.69    $false | (~spl7_2 | spl7_16)),
% 0.61/0.69    inference(resolution,[],[f225,f91])).
% 0.61/0.69  fof(f225,plain,(
% 0.61/0.69    ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) | spl7_16),
% 0.61/0.69    inference(avatar_component_clause,[],[f223])).
% 0.61/0.69  fof(f230,plain,(
% 0.61/0.69    ~spl7_14 | ~spl7_15 | ~spl7_16 | ~spl7_3 | spl7_17 | ~spl7_13),
% 0.61/0.69    inference(avatar_split_clause,[],[f212,f185,f227,f112,f223,f219,f215])).
% 0.61/0.69  fof(f212,plain,(
% 0.61/0.69    v3_pre_topc(sK4,sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK3))) | ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),k2_struct_0(sK3)) | ~r2_hidden(sK6(k2_struct_0(sK3),sK4,sK4),sK4) | ~spl7_13),
% 0.61/0.69    inference(resolution,[],[f209,f65])).
% 0.61/0.69  fof(f209,plain,(
% 0.61/0.69    ( ! [X6] : (~v3_pre_topc(X6,sK1) | v3_pre_topc(X6,sK3) | ~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(X6,k1_zfmisc_1(k2_struct_0(sK3))) | ~r2_hidden(sK6(k2_struct_0(sK3),X6,X6),k2_struct_0(sK3)) | ~r2_hidden(sK6(k2_struct_0(sK3),X6,X6),X6)) ) | ~spl7_13),
% 0.61/0.69    inference(superposition,[],[f186,f201])).
% 0.61/0.69  fof(f201,plain,(
% 0.61/0.69    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK6(X0,X1,X1),X0) | ~r2_hidden(sK6(X0,X1,X1),X1)) )),
% 0.61/0.69    inference(duplicate_literal_removal,[],[f200])).
% 0.61/0.69  fof(f200,plain,(
% 0.61/0.69    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1,X1),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X1 | ~r2_hidden(sK6(X0,X1,X1),X1) | k1_setfam_1(k2_tarski(X1,X0)) = X1) )),
% 0.61/0.69    inference(resolution,[],[f194,f68])).
% 0.61/0.69  fof(f194,plain,(
% 0.61/0.69    ( ! [X6,X7] : (sP0(X6,X7,X7) | ~r2_hidden(sK6(X6,X7,X7),X6) | k1_setfam_1(k2_tarski(X7,X6)) = X7 | ~r2_hidden(sK6(X6,X7,X7),X7)) )),
% 0.61/0.69    inference(resolution,[],[f152,f94])).
% 0.61/0.69  fof(f152,plain,(
% 0.61/0.69    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | k1_setfam_1(k2_tarski(X1,X0)) = X2) )),
% 0.61/0.69    inference(resolution,[],[f62,f68])).
% 0.61/0.69  fof(f62,plain,(
% 0.61/0.69    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.61/0.69    inference(cnf_transformation,[],[f36])).
% 0.61/0.69  fof(f189,plain,(
% 0.61/0.69    spl7_12),
% 0.61/0.69    inference(avatar_contradiction_clause,[],[f188])).
% 0.61/0.69  fof(f188,plain,(
% 0.61/0.69    $false | spl7_12),
% 0.61/0.69    inference(resolution,[],[f183,f72])).
% 0.61/0.69  fof(f72,plain,(
% 0.61/0.69    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.61/0.69    inference(forward_demodulation,[],[f46,f45])).
% 0.61/0.69  fof(f45,plain,(
% 0.61/0.69    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.61/0.69    inference(cnf_transformation,[],[f2])).
% 0.61/0.69  fof(f2,axiom,(
% 0.61/0.69    ! [X0] : k2_subset_1(X0) = X0),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.61/0.69  fof(f46,plain,(
% 0.61/0.69    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.61/0.69    inference(cnf_transformation,[],[f3])).
% 0.61/0.69  fof(f3,axiom,(
% 0.61/0.69    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.61/0.69  fof(f183,plain,(
% 0.61/0.69    ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) | spl7_12),
% 0.61/0.69    inference(avatar_component_clause,[],[f181])).
% 0.61/0.69  fof(f181,plain,(
% 0.61/0.69    spl7_12 <=> m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))),
% 0.61/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.61/0.69  fof(f187,plain,(
% 0.61/0.69    ~spl7_12 | spl7_13 | ~spl7_11),
% 0.61/0.69    inference(avatar_split_clause,[],[f179,f176,f185,f181])).
% 0.61/0.69  fof(f176,plain,(
% 0.61/0.69    spl7_11 <=> ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))))),
% 0.61/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.61/0.69  fof(f179,plain,(
% 0.61/0.69    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | v3_pre_topc(k1_setfam_1(k2_tarski(X0,k2_struct_0(sK3))),sK3) | ~m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3)))) ) | ~spl7_11),
% 0.61/0.69    inference(superposition,[],[f177,f67])).
% 0.61/0.69  fof(f67,plain,(
% 0.61/0.69    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.61/0.69    inference(definition_unfolding,[],[f56,f54])).
% 0.61/0.69  fof(f56,plain,(
% 0.61/0.69    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.61/0.69    inference(cnf_transformation,[],[f20])).
% 0.61/0.69  fof(f20,plain,(
% 0.61/0.69    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.61/0.69    inference(ennf_transformation,[],[f5])).
% 0.61/0.69  fof(f5,axiom,(
% 0.61/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.61/0.69  fof(f177,plain,(
% 0.61/0.69    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3)) ) | ~spl7_11),
% 0.61/0.69    inference(avatar_component_clause,[],[f176])).
% 0.61/0.69  fof(f178,plain,(
% 0.61/0.69    ~spl7_1 | spl7_11 | ~spl7_2),
% 0.61/0.69    inference(avatar_split_clause,[],[f174,f84,f176,f80])).
% 0.61/0.69  fof(f80,plain,(
% 0.61/0.69    spl7_1 <=> l1_pre_topc(sK1)),
% 0.61/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.61/0.69  fof(f174,plain,(
% 0.61/0.69    ( ! [X0] : (v3_pre_topc(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~l1_pre_topc(sK1)) ) | ~spl7_2),
% 0.61/0.69    inference(forward_demodulation,[],[f173,f86])).
% 0.61/0.69  fof(f173,plain,(
% 0.61/0.69    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(k2_struct_0(sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) | ~l1_pre_topc(sK1)) ) | ~spl7_2),
% 0.61/0.69    inference(forward_demodulation,[],[f172,f86])).
% 0.61/0.69  fof(f172,plain,(
% 0.61/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK1))) | ~v3_pre_topc(X0,sK1) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) | ~l1_pre_topc(sK1)) )),
% 0.61/0.69    inference(forward_demodulation,[],[f171,f74])).
% 0.61/0.69  fof(f74,plain,(
% 0.61/0.69    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.61/0.69    inference(resolution,[],[f73,f38])).
% 0.61/0.69  fof(f38,plain,(
% 0.61/0.69    l1_pre_topc(sK1)),
% 0.61/0.69    inference(cnf_transformation,[],[f27])).
% 0.61/0.69  fof(f73,plain,(
% 0.61/0.69    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.61/0.69    inference(resolution,[],[f47,f48])).
% 0.61/0.69  fof(f48,plain,(
% 0.61/0.69    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.61/0.69    inference(cnf_transformation,[],[f16])).
% 0.61/0.69  fof(f16,plain,(
% 0.61/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.61/0.69    inference(ennf_transformation,[],[f8])).
% 0.61/0.69  fof(f8,axiom,(
% 0.61/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.61/0.69  fof(f47,plain,(
% 0.61/0.69    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.61/0.69    inference(cnf_transformation,[],[f15])).
% 0.61/0.69  fof(f15,plain,(
% 0.61/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.61/0.69    inference(ennf_transformation,[],[f7])).
% 0.61/0.69  fof(f7,axiom,(
% 0.61/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.61/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.61/0.69  fof(f171,plain,(
% 0.61/0.69    ( ! [X0] : (~v3_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) | v3_pre_topc(k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)),sK3) | ~l1_pre_topc(sK1)) )),
% 0.61/0.69    inference(resolution,[],[f70,f40])).
% 0.61/0.69  fof(f40,plain,(
% 0.61/0.69    m1_pre_topc(sK3,sK1)),
% 0.61/0.69    inference(cnf_transformation,[],[f27])).
% 0.61/0.69  fof(f70,plain,(
% 0.61/0.69    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.61/0.69    inference(equality_resolution,[],[f53])).
% 0.61/0.69  fof(f53,plain,(
% 0.61/0.69    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.61/0.69    inference(cnf_transformation,[],[f31])).
% 0.61/0.69  fof(f31,plain,(
% 0.61/0.69    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.61/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f29,f30])).
% 0.61/0.69  fof(f30,plain,(
% 0.61/0.69    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.61/0.69    introduced(choice_axiom,[])).
% 0.61/0.69  fof(f29,plain,(
% 0.61/0.69    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.61/0.69    inference(rectify,[],[f28])).
% 0.61/0.69  fof(f28,plain,(
% 0.61/0.69    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.61/0.69    inference(nnf_transformation,[],[f18])).
% 0.61/0.69  fof(f18,plain,(
% 0.61/0.69    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.61/0.69    inference(ennf_transformation,[],[f10])).
% 0.61/0.70  fof(f10,axiom,(
% 0.61/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.61/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).
% 0.61/0.70  fof(f125,plain,(
% 0.61/0.70    spl7_3),
% 0.61/0.70    inference(avatar_contradiction_clause,[],[f124])).
% 0.61/0.70  fof(f124,plain,(
% 0.61/0.70    $false | spl7_3),
% 0.61/0.70    inference(resolution,[],[f114,f76])).
% 0.61/0.70  fof(f76,plain,(
% 0.61/0.70    m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1)))),
% 0.61/0.70    inference(backward_demodulation,[],[f66,f74])).
% 0.61/0.70  fof(f66,plain,(
% 0.61/0.70    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.61/0.70    inference(definition_unfolding,[],[f39,f43])).
% 0.61/0.70  fof(f39,plain,(
% 0.61/0.70    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.61/0.70    inference(cnf_transformation,[],[f27])).
% 0.61/0.70  fof(f114,plain,(
% 0.61/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(k2_struct_0(sK1))) | spl7_3),
% 0.61/0.70    inference(avatar_component_clause,[],[f112])).
% 0.61/0.70  fof(f90,plain,(
% 0.61/0.70    spl7_1),
% 0.61/0.70    inference(avatar_contradiction_clause,[],[f88])).
% 0.61/0.70  fof(f88,plain,(
% 0.61/0.70    $false | spl7_1),
% 0.61/0.70    inference(resolution,[],[f82,f38])).
% 0.61/0.70  fof(f82,plain,(
% 0.61/0.70    ~l1_pre_topc(sK1) | spl7_1),
% 0.61/0.70    inference(avatar_component_clause,[],[f80])).
% 0.61/0.70  fof(f87,plain,(
% 0.61/0.70    ~spl7_1 | spl7_2),
% 0.61/0.70    inference(avatar_split_clause,[],[f78,f84,f80])).
% 0.61/0.70  fof(f78,plain,(
% 0.61/0.70    u1_struct_0(sK3) = k2_struct_0(sK3) | ~l1_pre_topc(sK1)),
% 0.61/0.70    inference(resolution,[],[f75,f40])).
% 0.61/0.70  % (24156)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.61/0.70  fof(f75,plain,(
% 0.61/0.70    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | k2_struct_0(X0) = u1_struct_0(X0) | ~l1_pre_topc(X1)) )),
% 0.61/0.70    inference(resolution,[],[f73,f49])).
% 0.61/0.70  fof(f49,plain,(
% 0.61/0.70    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.61/0.70    inference(cnf_transformation,[],[f17])).
% 0.61/0.70  fof(f17,plain,(
% 0.61/0.70    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.61/0.70    inference(ennf_transformation,[],[f9])).
% 0.61/0.70  fof(f9,axiom,(
% 0.61/0.70    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.61/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.61/0.70  % SZS output end Proof for theBenchmark
% 0.61/0.70  % (24143)------------------------------
% 0.61/0.70  % (24143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.61/0.70  % (24143)Termination reason: Refutation
% 0.61/0.70  
% 0.61/0.70  % (24143)Memory used [KB]: 6396
% 0.61/0.70  % (24143)Time elapsed: 0.122 s
% 0.61/0.70  % (24143)------------------------------
% 0.61/0.70  % (24143)------------------------------
% 0.61/0.70  % (23997)Success in time 0.337 s
%------------------------------------------------------------------------------
