%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 369 expanded)
%              Number of leaves         :   33 ( 134 expanded)
%              Depth                    :   17
%              Number of atoms          :  598 (2422 expanded)
%              Number of equality atoms :   53 ( 295 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f108,f135,f138,f149,f156,f174,f197,f199,f211,f213,f248,f271,f280,f345,f386,f513,f514])).

fof(f514,plain,
    ( ~ spl7_11
    | ~ spl7_16
    | spl7_14
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f373,f82,f167,f194,f141])).

fof(f141,plain,
    ( spl7_11
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f194,plain,
    ( spl7_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f167,plain,
    ( spl7_14
  <=> k1_xboole_0 = k1_tops_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f82,plain,
    ( spl7_1
  <=> v2_tops_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f373,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f83,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f83,plain,
    ( v2_tops_1(sK3,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f513,plain,
    ( ~ spl7_4
    | spl7_10
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(avatar_contradiction_clause,[],[f508])).

fof(f508,plain,
    ( $false
    | ~ spl7_4
    | spl7_10
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(resolution,[],[f507,f133])).

fof(f133,plain,
    ( ~ r1_tarski(sK4,k1_xboole_0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_10
  <=> r1_tarski(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f507,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(duplicate_literal_removal,[],[f504])).

fof(f504,plain,
    ( r1_tarski(sK4,k1_xboole_0)
    | r1_tarski(sK4,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(resolution,[],[f498,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f498,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(sK4,X0),k1_xboole_0)
        | r1_tarski(sK4,X0) )
    | ~ spl7_4
    | ~ spl7_13
    | ~ spl7_14
    | ~ spl7_32 ),
    inference(resolution,[],[f497,f175])).

fof(f175,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK3,sK2)
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl7_13
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f159,f169])).

fof(f169,plain,
    ( k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK3,sK2)
        | r2_hidden(X0,k1_tops_1(sK2,sK3)) )
    | ~ spl7_13 ),
    inference(resolution,[],[f157,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X2,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k1_tops_1(X0,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X2,k1_tops_1(X0,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X1,k1_tops_1(X0,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f157,plain,
    ( ! [X0] : sP1(sK2,sK3,X0)
    | ~ spl7_13 ),
    inference(resolution,[],[f155,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ( k1_xboole_0 != sK4
        & v3_pre_topc(sK4,sK2)
        & r1_tarski(sK4,sK3)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
      | ~ v2_tops_1(sK3,sK2) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK2)
          | ~ r1_tarski(X3,sK3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      | v2_tops_1(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK2)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
            | ~ v2_tops_1(X1,sK2) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK2)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            | v2_tops_1(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK2)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          | ~ v2_tops_1(X1,sK2) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK2)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
          | v2_tops_1(X1,sK2) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK2)
            & r1_tarski(X2,sK3)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        | ~ v2_tops_1(sK3,sK2) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK2)
            | ~ r1_tarski(X3,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
        | v2_tops_1(sK3,sK2) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK2)
        & r1_tarski(X2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( k1_xboole_0 != sK4
      & v3_pre_topc(sK4,sK2)
      & r1_tarski(sK4,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

% (16461)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK2,X0,X1) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f497,plain,
    ( ! [X1] :
        ( sP0(sK6(sK4,X1),sK3,sK2)
        | r1_tarski(sK4,X1) )
    | ~ spl7_4
    | ~ spl7_32 ),
    inference(resolution,[],[f446,f98])).

fof(f98,plain,
    ( r1_tarski(sK4,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl7_4
  <=> r1_tarski(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f446,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK4,X1)
        | sP0(sK6(sK4,X0),X1,sK2)
        | r1_tarski(sK4,X0) )
    | ~ spl7_32 ),
    inference(resolution,[],[f385,f74])).

% (16480)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK4)
        | sP0(X0,X1,sK2)
        | ~ r1_tarski(sK4,X1) )
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f384])).

fof(f384,plain,
    ( spl7_32
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK4)
        | sP0(X0,X1,sK2)
        | ~ r1_tarski(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f386,plain,
    ( ~ spl7_5
    | spl7_32
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f376,f91,f384,f101])).

fof(f101,plain,
    ( spl7_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f91,plain,
    ( spl7_3
  <=> v3_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f376,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK4)
        | ~ r1_tarski(sK4,X1)
        | sP0(X0,X1,sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f93,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(X3,X2)
      | ~ r2_hidden(X0,X3)
      | ~ r1_tarski(X3,X1)
      | sP0(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ( r2_hidden(X0,sK5(X0,X1,X2))
          & r1_tarski(sK5(X0,X1,X2),X1)
          & v3_pre_topc(sK5(X0,X1,X2),X2)
          & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X0,X4)
          & r1_tarski(X4,X1)
          & v3_pre_topc(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X0,sK5(X0,X1,X2))
        & r1_tarski(sK5(X0,X1,X2),X1)
        & v3_pre_topc(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ~ r2_hidden(X0,X3)
            | ~ r1_tarski(X3,X1)
            | ~ v3_pre_topc(X3,X2)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ? [X4] :
            ( r2_hidden(X0,X4)
            & r1_tarski(X4,X1)
            & v3_pre_topc(X4,X2)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ~ r2_hidden(X1,X3)
            | ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ? [X3] :
            ( r2_hidden(X1,X3)
            & r1_tarski(X3,X2)
            & v3_pre_topc(X3,X0)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f93,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f345,plain,
    ( ~ spl7_15
    | spl7_18
    | ~ spl7_21 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl7_15
    | spl7_18
    | ~ spl7_21 ),
    inference(resolution,[],[f337,f209])).

fof(f209,plain,
    ( ~ r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
    | spl7_18 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_18
  <=> r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f337,plain,
    ( r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(resolution,[],[f286,f75])).

fof(f286,plain,
    ( r2_hidden(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),k1_xboole_0)
    | ~ spl7_15
    | ~ spl7_21 ),
    inference(backward_demodulation,[],[f215,f239])).

fof(f239,plain,
    ( k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl7_21
  <=> k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f215,plain,
    ( r2_hidden(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2))
    | ~ spl7_15 ),
    inference(resolution,[],[f173,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X0,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f173,plain,
    ( sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_15
  <=> sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f280,plain,
    ( ~ spl7_15
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl7_15
    | spl7_23 ),
    inference(resolution,[],[f277,f173])).

fof(f277,plain,
    ( ~ sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)
    | spl7_23 ),
    inference(resolution,[],[f247,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f247,plain,
    ( ~ m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl7_23
  <=> m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f271,plain,
    ( ~ spl7_15
    | spl7_22 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl7_15
    | spl7_22 ),
    inference(resolution,[],[f243,f216])).

fof(f216,plain,
    ( r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3)
    | ~ spl7_15 ),
    inference(resolution,[],[f173,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_tarski(sK5(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f243,plain,
    ( ~ r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl7_22
  <=> r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f248,plain,
    ( spl7_21
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f234,f171,f106,f245,f241,f237])).

fof(f106,plain,
    ( spl7_6
  <=> ! [X3] :
        ( k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X3,sK3)
        | ~ v3_pre_topc(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f234,plain,
    ( ~ m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3)
    | k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)
    | ~ spl7_6
    | ~ spl7_15 ),
    inference(resolution,[],[f217,f107])).

fof(f107,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ r1_tarski(X3,sK3)
        | k1_xboole_0 = X3 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f217,plain,
    ( v3_pre_topc(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK2)
    | ~ spl7_15 ),
    inference(resolution,[],[f173,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f213,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl7_17 ),
    inference(resolution,[],[f205,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f205,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl7_17
  <=> r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f211,plain,
    ( ~ spl7_18
    | ~ spl7_17
    | spl7_14 ),
    inference(avatar_split_clause,[],[f201,f167,f203,f207])).

fof(f201,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3))
    | ~ r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)
    | spl7_14 ),
    inference(extensionality_resolution,[],[f72,f168])).

fof(f168,plain,
    ( k1_xboole_0 != k1_tops_1(sK2,sK3)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f167])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f199,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f198])).

fof(f198,plain,
    ( $false
    | spl7_16 ),
    inference(resolution,[],[f196,f49])).

fof(f196,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f197,plain,
    ( spl7_1
    | ~ spl7_16
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f192,f167,f194,f82])).

fof(f192,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_1(sK3,sK2)
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tops_1(sK3,sK2)
    | ~ spl7_14 ),
    inference(superposition,[],[f188,f169])).

fof(f188,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_tops_1(sK2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(X0,sK2) ) ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f174,plain,
    ( spl7_14
    | spl7_15
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f162,f154,f171,f167])).

fof(f162,plain,
    ( sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)
    | k1_xboole_0 = k1_tops_1(sK2,sK3)
    | ~ spl7_13 ),
    inference(resolution,[],[f161,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f161,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tops_1(sK2,sK3),X0)
        | sP0(sK6(k1_tops_1(sK2,sK3),X0),sK3,sK2) )
    | ~ spl7_13 ),
    inference(resolution,[],[f160,f74])).

fof(f160,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK2,sK3))
        | sP0(X1,sK3,sK2) )
    | ~ spl7_13 ),
    inference(resolution,[],[f157,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_tops_1(X0,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f156,plain,
    ( ~ spl7_11
    | spl7_13 ),
    inference(avatar_split_clause,[],[f152,f154,f141])).

fof(f152,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | sP1(sK2,X0,X1) ) ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X0,X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f25,f24])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f149,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl7_11 ),
    inference(resolution,[],[f143,f48])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f138,plain,(
    spl7_9 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl7_9 ),
    inference(resolution,[],[f129,f55])).

fof(f129,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_9
  <=> r1_tarski(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f135,plain,
    ( ~ spl7_10
    | ~ spl7_9
    | spl7_2 ),
    inference(avatar_split_clause,[],[f123,f86,f127,f131])).

fof(f86,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f123,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ r1_tarski(sK4,k1_xboole_0)
    | spl7_2 ),
    inference(extensionality_resolution,[],[f72,f88])).

fof(f88,plain,
    ( k1_xboole_0 != sK4
    | spl7_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f108,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f50,f106,f82])).

fof(f50,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_tops_1(sK3,sK2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f51,f101,f82])).

fof(f51,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f52,f96,f82])).

fof(f52,plain,
    ( r1_tarski(sK4,sK3)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

% (16475)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f94,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f53,f91,f82])).

fof(f53,plain,
    ( v3_pre_topc(sK4,sK2)
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f54,f86,f82])).

fof(f54,plain,
    ( k1_xboole_0 != sK4
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16477)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (16456)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (16455)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (16459)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (16462)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (16454)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (16464)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16457)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (16470)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (16464)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (16478)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (16453)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (16476)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (16472)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (16463)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f515,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f108,f135,f138,f149,f156,f174,f197,f199,f211,f213,f248,f271,f280,f345,f386,f513,f514])).
% 1.40/0.54  fof(f514,plain,(
% 1.40/0.54    ~spl7_11 | ~spl7_16 | spl7_14 | ~spl7_1),
% 1.40/0.54    inference(avatar_split_clause,[],[f373,f82,f167,f194,f141])).
% 1.40/0.54  fof(f141,plain,(
% 1.40/0.54    spl7_11 <=> l1_pre_topc(sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.40/0.54  fof(f194,plain,(
% 1.40/0.54    spl7_16 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.40/0.54  fof(f167,plain,(
% 1.40/0.54    spl7_14 <=> k1_xboole_0 = k1_tops_1(sK2,sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.40/0.54  fof(f82,plain,(
% 1.40/0.54    spl7_1 <=> v2_tops_1(sK3,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.40/0.54  fof(f373,plain,(
% 1.40/0.54    k1_xboole_0 = k1_tops_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | ~spl7_1),
% 1.40/0.54    inference(resolution,[],[f83,f56])).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(nnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f9])).
% 1.40/0.54  fof(f9,axiom,(
% 1.40/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.40/0.54  fof(f83,plain,(
% 1.40/0.54    v2_tops_1(sK3,sK2) | ~spl7_1),
% 1.40/0.54    inference(avatar_component_clause,[],[f82])).
% 1.40/0.54  fof(f513,plain,(
% 1.40/0.54    ~spl7_4 | spl7_10 | ~spl7_13 | ~spl7_14 | ~spl7_32),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f508])).
% 1.40/0.54  fof(f508,plain,(
% 1.40/0.54    $false | (~spl7_4 | spl7_10 | ~spl7_13 | ~spl7_14 | ~spl7_32)),
% 1.40/0.54    inference(resolution,[],[f507,f133])).
% 1.40/0.54  fof(f133,plain,(
% 1.40/0.54    ~r1_tarski(sK4,k1_xboole_0) | spl7_10),
% 1.40/0.54    inference(avatar_component_clause,[],[f131])).
% 1.40/0.54  fof(f131,plain,(
% 1.40/0.54    spl7_10 <=> r1_tarski(sK4,k1_xboole_0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.40/0.54  fof(f507,plain,(
% 1.40/0.54    r1_tarski(sK4,k1_xboole_0) | (~spl7_4 | ~spl7_13 | ~spl7_14 | ~spl7_32)),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f504])).
% 1.40/0.54  fof(f504,plain,(
% 1.40/0.54    r1_tarski(sK4,k1_xboole_0) | r1_tarski(sK4,k1_xboole_0) | (~spl7_4 | ~spl7_13 | ~spl7_14 | ~spl7_32)),
% 1.40/0.54    inference(resolution,[],[f498,f75])).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f46])).
% 1.40/0.54  fof(f46,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f44,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.54    inference(rectify,[],[f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.40/0.54    inference(nnf_transformation,[],[f22])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.40/0.54  fof(f498,plain,(
% 1.40/0.54    ( ! [X0] : (r2_hidden(sK6(sK4,X0),k1_xboole_0) | r1_tarski(sK4,X0)) ) | (~spl7_4 | ~spl7_13 | ~spl7_14 | ~spl7_32)),
% 1.40/0.54    inference(resolution,[],[f497,f175])).
% 1.40/0.54  fof(f175,plain,(
% 1.40/0.54    ( ! [X0] : (~sP0(X0,sK3,sK2) | r2_hidden(X0,k1_xboole_0)) ) | (~spl7_13 | ~spl7_14)),
% 1.40/0.54    inference(backward_demodulation,[],[f159,f169])).
% 1.40/0.54  fof(f169,plain,(
% 1.40/0.54    k1_xboole_0 = k1_tops_1(sK2,sK3) | ~spl7_14),
% 1.40/0.54    inference(avatar_component_clause,[],[f167])).
% 1.40/0.54  fof(f159,plain,(
% 1.40/0.54    ( ! [X0] : (~sP0(X0,sK3,sK2) | r2_hidden(X0,k1_tops_1(sK2,sK3))) ) | ~spl7_13),
% 1.40/0.54    inference(resolution,[],[f157,f63])).
% 1.40/0.54  fof(f63,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X2,k1_tops_1(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (((r2_hidden(X2,k1_tops_1(X0,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X2,k1_tops_1(X0,X1)))) | ~sP1(X0,X1,X2))),
% 1.40/0.54    inference(rectify,[],[f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    ! [X0,X2,X1] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~sP1(X0,X2,X1))),
% 1.40/0.54    inference(nnf_transformation,[],[f25])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ! [X0,X2,X1] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.40/0.54  fof(f157,plain,(
% 1.40/0.54    ( ! [X0] : (sP1(sK2,sK3,X0)) ) | ~spl7_13),
% 1.40/0.54    inference(resolution,[],[f155,f49])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    (((k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(X1,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) | ~v2_tops_1(sK3,sK2)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK2) & r1_tarski(X2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (k1_xboole_0 != sK4 & v3_pre_topc(sK4,sK2) & r1_tarski(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.40/0.54    inference(rectify,[],[f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f27])).
% 1.40/0.54  % (16461)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.40/0.54    inference(nnf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f12])).
% 1.40/0.54  fof(f12,plain,(
% 1.40/0.54    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f11])).
% 1.40/0.54  fof(f11,negated_conjecture,(
% 1.40/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.40/0.54    inference(negated_conjecture,[],[f10])).
% 1.40/0.54  fof(f10,conjecture,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 1.40/0.54  fof(f155,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0,X1)) ) | ~spl7_13),
% 1.40/0.54    inference(avatar_component_clause,[],[f154])).
% 1.40/0.54  fof(f154,plain,(
% 1.40/0.54    spl7_13 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0,X1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.40/0.54  fof(f497,plain,(
% 1.40/0.54    ( ! [X1] : (sP0(sK6(sK4,X1),sK3,sK2) | r1_tarski(sK4,X1)) ) | (~spl7_4 | ~spl7_32)),
% 1.40/0.54    inference(resolution,[],[f446,f98])).
% 1.40/0.54  fof(f98,plain,(
% 1.40/0.54    r1_tarski(sK4,sK3) | ~spl7_4),
% 1.40/0.54    inference(avatar_component_clause,[],[f96])).
% 1.40/0.54  fof(f96,plain,(
% 1.40/0.54    spl7_4 <=> r1_tarski(sK4,sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.40/0.54  fof(f446,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(sK4,X1) | sP0(sK6(sK4,X0),X1,sK2) | r1_tarski(sK4,X0)) ) | ~spl7_32),
% 1.40/0.54    inference(resolution,[],[f385,f74])).
% 1.40/0.54  % (16480)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.54  fof(f74,plain,(
% 1.40/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f46])).
% 1.40/0.54  fof(f385,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK4) | sP0(X0,X1,sK2) | ~r1_tarski(sK4,X1)) ) | ~spl7_32),
% 1.40/0.54    inference(avatar_component_clause,[],[f384])).
% 1.40/0.54  fof(f384,plain,(
% 1.40/0.54    spl7_32 <=> ! [X1,X0] : (~r2_hidden(X0,sK4) | sP0(X0,X1,sK2) | ~r1_tarski(sK4,X1))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.40/0.54  fof(f386,plain,(
% 1.40/0.54    ~spl7_5 | spl7_32 | ~spl7_3),
% 1.40/0.54    inference(avatar_split_clause,[],[f376,f91,f384,f101])).
% 1.40/0.54  fof(f101,plain,(
% 1.40/0.54    spl7_5 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.40/0.54  fof(f91,plain,(
% 1.40/0.54    spl7_3 <=> v3_pre_topc(sK4,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.40/0.54  fof(f376,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r2_hidden(X0,sK4) | ~r1_tarski(sK4,X1) | sP0(X0,X1,sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_3),
% 1.40/0.54    inference(resolution,[],[f93,f68])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(X3,X2) | ~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | sP0(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.40/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 1.40/0.54    introduced(choice_axiom,[])).
% 1.40/0.54  fof(f38,plain,(
% 1.40/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 1.40/0.54    inference(rectify,[],[f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 1.40/0.54    inference(nnf_transformation,[],[f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.40/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.54  fof(f93,plain,(
% 1.40/0.54    v3_pre_topc(sK4,sK2) | ~spl7_3),
% 1.40/0.54    inference(avatar_component_clause,[],[f91])).
% 1.40/0.54  fof(f345,plain,(
% 1.40/0.54    ~spl7_15 | spl7_18 | ~spl7_21),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f340])).
% 1.40/0.54  fof(f340,plain,(
% 1.40/0.54    $false | (~spl7_15 | spl7_18 | ~spl7_21)),
% 1.40/0.54    inference(resolution,[],[f337,f209])).
% 1.40/0.54  fof(f209,plain,(
% 1.40/0.54    ~r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0) | spl7_18),
% 1.40/0.54    inference(avatar_component_clause,[],[f207])).
% 1.40/0.54  fof(f207,plain,(
% 1.40/0.54    spl7_18 <=> r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.40/0.54  fof(f337,plain,(
% 1.40/0.54    r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0) | (~spl7_15 | ~spl7_21)),
% 1.40/0.54    inference(resolution,[],[f286,f75])).
% 1.40/0.54  fof(f286,plain,(
% 1.40/0.54    r2_hidden(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),k1_xboole_0) | (~spl7_15 | ~spl7_21)),
% 1.40/0.54    inference(backward_demodulation,[],[f215,f239])).
% 1.40/0.54  fof(f239,plain,(
% 1.40/0.54    k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) | ~spl7_21),
% 1.40/0.54    inference(avatar_component_clause,[],[f237])).
% 1.40/0.54  fof(f237,plain,(
% 1.40/0.54    spl7_21 <=> k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 1.40/0.54  fof(f215,plain,(
% 1.40/0.54    r2_hidden(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)) | ~spl7_15),
% 1.40/0.54    inference(resolution,[],[f173,f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X0,sK5(X0,X1,X2))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f173,plain,(
% 1.40/0.54    sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) | ~spl7_15),
% 1.40/0.54    inference(avatar_component_clause,[],[f171])).
% 1.40/0.54  fof(f171,plain,(
% 1.40/0.54    spl7_15 <=> sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.40/0.54  fof(f280,plain,(
% 1.40/0.54    ~spl7_15 | spl7_23),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f279])).
% 1.40/0.54  fof(f279,plain,(
% 1.40/0.54    $false | (~spl7_15 | spl7_23)),
% 1.40/0.54    inference(resolution,[],[f277,f173])).
% 1.40/0.54  fof(f277,plain,(
% 1.40/0.54    ~sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) | spl7_23),
% 1.40/0.54    inference(resolution,[],[f247,f64])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f247,plain,(
% 1.40/0.54    ~m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_23),
% 1.40/0.54    inference(avatar_component_clause,[],[f245])).
% 1.40/0.54  fof(f245,plain,(
% 1.40/0.54    spl7_23 <=> m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.40/0.54  fof(f271,plain,(
% 1.40/0.54    ~spl7_15 | spl7_22),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f270])).
% 1.40/0.54  fof(f270,plain,(
% 1.40/0.54    $false | (~spl7_15 | spl7_22)),
% 1.40/0.54    inference(resolution,[],[f243,f216])).
% 1.40/0.54  fof(f216,plain,(
% 1.40/0.54    r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3) | ~spl7_15),
% 1.40/0.54    inference(resolution,[],[f173,f66])).
% 1.40/0.54  fof(f66,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_tarski(sK5(X0,X1,X2),X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f243,plain,(
% 1.40/0.54    ~r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3) | spl7_22),
% 1.40/0.54    inference(avatar_component_clause,[],[f241])).
% 1.40/0.54  fof(f241,plain,(
% 1.40/0.54    spl7_22 <=> r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.40/0.54  fof(f248,plain,(
% 1.40/0.54    spl7_21 | ~spl7_22 | ~spl7_23 | ~spl7_6 | ~spl7_15),
% 1.40/0.54    inference(avatar_split_clause,[],[f234,f171,f106,f245,f241,f237])).
% 1.40/0.54  fof(f106,plain,(
% 1.40/0.54    spl7_6 <=> ! [X3] : (k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X3,sK3) | ~v3_pre_topc(X3,sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.40/0.54  fof(f234,plain,(
% 1.40/0.54    ~m1_subset_1(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK3) | k1_xboole_0 = sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) | (~spl7_6 | ~spl7_15)),
% 1.40/0.54    inference(resolution,[],[f217,f107])).
% 1.40/0.54  fof(f107,plain,(
% 1.40/0.54    ( ! [X3] : (~v3_pre_topc(X3,sK2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | ~r1_tarski(X3,sK3) | k1_xboole_0 = X3) ) | ~spl7_6),
% 1.40/0.54    inference(avatar_component_clause,[],[f106])).
% 1.40/0.54  fof(f217,plain,(
% 1.40/0.54    v3_pre_topc(sK5(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2),sK2) | ~spl7_15),
% 1.40/0.54    inference(resolution,[],[f173,f65])).
% 1.40/0.54  fof(f65,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(sK5(X0,X1,X2),X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f40])).
% 1.40/0.54  fof(f213,plain,(
% 1.40/0.54    spl7_17),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f212])).
% 1.40/0.54  fof(f212,plain,(
% 1.40/0.54    $false | spl7_17),
% 1.40/0.54    inference(resolution,[],[f205,f55])).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.54  fof(f205,plain,(
% 1.40/0.54    ~r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3)) | spl7_17),
% 1.40/0.54    inference(avatar_component_clause,[],[f203])).
% 1.40/0.54  fof(f203,plain,(
% 1.40/0.54    spl7_17 <=> r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.40/0.54  fof(f211,plain,(
% 1.40/0.54    ~spl7_18 | ~spl7_17 | spl7_14),
% 1.40/0.54    inference(avatar_split_clause,[],[f201,f167,f203,f207])).
% 1.40/0.54  fof(f201,plain,(
% 1.40/0.54    ~r1_tarski(k1_xboole_0,k1_tops_1(sK2,sK3)) | ~r1_tarski(k1_tops_1(sK2,sK3),k1_xboole_0) | spl7_14),
% 1.40/0.54    inference(extensionality_resolution,[],[f72,f168])).
% 1.40/0.54  fof(f168,plain,(
% 1.40/0.54    k1_xboole_0 != k1_tops_1(sK2,sK3) | spl7_14),
% 1.40/0.54    inference(avatar_component_clause,[],[f167])).
% 1.40/0.54  fof(f72,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.54    inference(flattening,[],[f41])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.54    inference(nnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.54  fof(f199,plain,(
% 1.40/0.54    spl7_16),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f198])).
% 1.40/0.54  fof(f198,plain,(
% 1.40/0.54    $false | spl7_16),
% 1.40/0.54    inference(resolution,[],[f196,f49])).
% 1.40/0.54  fof(f196,plain,(
% 1.40/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_16),
% 1.40/0.54    inference(avatar_component_clause,[],[f194])).
% 1.40/0.54  fof(f197,plain,(
% 1.40/0.54    spl7_1 | ~spl7_16 | ~spl7_14),
% 1.40/0.54    inference(avatar_split_clause,[],[f192,f167,f194,f82])).
% 1.40/0.54  fof(f192,plain,(
% 1.40/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2) | ~spl7_14),
% 1.40/0.54    inference(trivial_inequality_removal,[],[f191])).
% 1.40/0.54  fof(f191,plain,(
% 1.40/0.54    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2) | ~spl7_14),
% 1.40/0.54    inference(superposition,[],[f188,f169])).
% 1.40/0.54  fof(f188,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 != k1_tops_1(sK2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(X0,sK2)) )),
% 1.40/0.54    inference(resolution,[],[f57,f48])).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    l1_pre_topc(sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f57,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tops_1(X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f34])).
% 1.40/0.54  fof(f174,plain,(
% 1.40/0.54    spl7_14 | spl7_15 | ~spl7_13),
% 1.40/0.54    inference(avatar_split_clause,[],[f162,f154,f171,f167])).
% 1.40/0.54  fof(f162,plain,(
% 1.40/0.54    sP0(sK6(k1_tops_1(sK2,sK3),k1_xboole_0),sK3,sK2) | k1_xboole_0 = k1_tops_1(sK2,sK3) | ~spl7_13),
% 1.40/0.54    inference(resolution,[],[f161,f59])).
% 1.40/0.54  fof(f59,plain,(
% 1.40/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.40/0.54    inference(cnf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,plain,(
% 1.40/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.40/0.54    inference(ennf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.40/0.54  fof(f161,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_tops_1(sK2,sK3),X0) | sP0(sK6(k1_tops_1(sK2,sK3),X0),sK3,sK2)) ) | ~spl7_13),
% 1.40/0.54    inference(resolution,[],[f160,f74])).
% 1.40/0.54  fof(f160,plain,(
% 1.40/0.54    ( ! [X1] : (~r2_hidden(X1,k1_tops_1(sK2,sK3)) | sP0(X1,sK3,sK2)) ) | ~spl7_13),
% 1.40/0.54    inference(resolution,[],[f157,f62])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X2,k1_tops_1(X0,X1)) | sP0(X2,X1,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f36])).
% 1.40/0.54  fof(f156,plain,(
% 1.40/0.54    ~spl7_11 | spl7_13),
% 1.40/0.54    inference(avatar_split_clause,[],[f152,f154,f141])).
% 1.40/0.54  fof(f152,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sP1(sK2,X0,X1)) )),
% 1.40/0.54    inference(resolution,[],[f69,f47])).
% 1.40/0.54  fof(f47,plain,(
% 1.40/0.54    v2_pre_topc(sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f69,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sP1(X0,X2,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ! [X0] : (! [X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.40/0.54    inference(definition_folding,[],[f21,f25,f24])).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.40/0.54    inference(flattening,[],[f20])).
% 1.40/0.54  fof(f20,plain,(
% 1.40/0.54    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.40/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 1.40/0.54  fof(f149,plain,(
% 1.40/0.54    spl7_11),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f148])).
% 1.40/0.54  fof(f148,plain,(
% 1.40/0.54    $false | spl7_11),
% 1.40/0.54    inference(resolution,[],[f143,f48])).
% 1.40/0.54  fof(f143,plain,(
% 1.40/0.54    ~l1_pre_topc(sK2) | spl7_11),
% 1.40/0.54    inference(avatar_component_clause,[],[f141])).
% 1.40/0.54  fof(f138,plain,(
% 1.40/0.54    spl7_9),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f137])).
% 1.40/0.54  fof(f137,plain,(
% 1.40/0.54    $false | spl7_9),
% 1.40/0.54    inference(resolution,[],[f129,f55])).
% 1.40/0.54  fof(f129,plain,(
% 1.40/0.54    ~r1_tarski(k1_xboole_0,sK4) | spl7_9),
% 1.40/0.54    inference(avatar_component_clause,[],[f127])).
% 1.40/0.54  fof(f127,plain,(
% 1.40/0.54    spl7_9 <=> r1_tarski(k1_xboole_0,sK4)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.40/0.54  fof(f135,plain,(
% 1.40/0.54    ~spl7_10 | ~spl7_9 | spl7_2),
% 1.40/0.54    inference(avatar_split_clause,[],[f123,f86,f127,f131])).
% 1.40/0.54  fof(f86,plain,(
% 1.40/0.54    spl7_2 <=> k1_xboole_0 = sK4),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.40/0.54  fof(f123,plain,(
% 1.40/0.54    ~r1_tarski(k1_xboole_0,sK4) | ~r1_tarski(sK4,k1_xboole_0) | spl7_2),
% 1.40/0.54    inference(extensionality_resolution,[],[f72,f88])).
% 1.40/0.54  fof(f88,plain,(
% 1.40/0.54    k1_xboole_0 != sK4 | spl7_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f86])).
% 1.40/0.54  fof(f108,plain,(
% 1.40/0.54    spl7_1 | spl7_6),
% 1.40/0.54    inference(avatar_split_clause,[],[f50,f106,f82])).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v2_tops_1(sK3,sK2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f104,plain,(
% 1.40/0.54    ~spl7_1 | spl7_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f51,f101,f82])).
% 1.40/0.54  fof(f51,plain,(
% 1.40/0.54    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | ~v2_tops_1(sK3,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f99,plain,(
% 1.40/0.54    ~spl7_1 | spl7_4),
% 1.40/0.54    inference(avatar_split_clause,[],[f52,f96,f82])).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    r1_tarski(sK4,sK3) | ~v2_tops_1(sK3,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  % (16475)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.54  fof(f94,plain,(
% 1.40/0.54    ~spl7_1 | spl7_3),
% 1.40/0.54    inference(avatar_split_clause,[],[f53,f91,f82])).
% 1.40/0.54  fof(f53,plain,(
% 1.40/0.54    v3_pre_topc(sK4,sK2) | ~v2_tops_1(sK3,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  fof(f89,plain,(
% 1.40/0.54    ~spl7_1 | ~spl7_2),
% 1.40/0.54    inference(avatar_split_clause,[],[f54,f86,f82])).
% 1.40/0.54  fof(f54,plain,(
% 1.40/0.54    k1_xboole_0 != sK4 | ~v2_tops_1(sK3,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f33])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (16464)------------------------------
% 1.40/0.54  % (16464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (16464)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (16464)Memory used [KB]: 6396
% 1.40/0.54  % (16464)Time elapsed: 0.138 s
% 1.40/0.54  % (16464)------------------------------
% 1.40/0.54  % (16464)------------------------------
% 1.40/0.54  % (16452)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (16451)Success in time 0.192 s
%------------------------------------------------------------------------------
