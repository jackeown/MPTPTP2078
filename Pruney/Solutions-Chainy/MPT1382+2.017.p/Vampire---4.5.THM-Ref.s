%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 359 expanded)
%              Number of leaves         :   35 ( 146 expanded)
%              Depth                    :    9
%              Number of atoms          :  628 (2322 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f892,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f99,f101,f168,f192,f230,f253,f309,f477,f489,f492,f509,f525,f538,f548,f561,f570,f583,f775,f871,f884,f891])).

fof(f891,plain,
    ( ~ spl7_40
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(avatar_contradiction_clause,[],[f890])).

fof(f890,plain,
    ( $false
    | ~ spl7_40
    | ~ spl7_46
    | ~ spl7_58 ),
    inference(resolution,[],[f870,f584])).

fof(f584,plain,
    ( r2_hidden(sK3,sK5(sK3,sK4,sK2))
    | ~ spl7_40
    | ~ spl7_46 ),
    inference(forward_demodulation,[],[f567,f520])).

fof(f520,plain,
    ( sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl7_40
  <=> sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f567,plain,
    ( r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl7_46
  <=> r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f870,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(sK3,sK4,sK2))
    | ~ spl7_58 ),
    inference(avatar_component_clause,[],[f869])).

fof(f869,plain,
    ( spl7_58
  <=> ! [X0] : ~ r2_hidden(X0,sK5(sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f884,plain,
    ( ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_57 ),
    inference(avatar_contradiction_clause,[],[f883])).

fof(f883,plain,
    ( $false
    | ~ spl7_40
    | ~ spl7_42
    | ~ spl7_46
    | ~ spl7_57 ),
    inference(resolution,[],[f877,f584])).

fof(f877,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(sK3,sK4,sK2))
    | ~ spl7_42
    | ~ spl7_57 ),
    inference(resolution,[],[f867,f613])).

fof(f613,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,sK5(sK3,sK4,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_42 ),
    inference(resolution,[],[f585,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f585,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK3,sK4,sK2)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_42 ),
    inference(resolution,[],[f529,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f529,plain,
    ( v1_xboole_0(sK5(sK3,sK4,sK2))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f527])).

fof(f527,plain,
    ( spl7_42
  <=> v1_xboole_0(sK5(sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f867,plain,
    ( r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2))
    | ~ spl7_57 ),
    inference(avatar_component_clause,[],[f865])).

% (9288)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f865,plain,
    ( spl7_57
  <=> r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f871,plain,
    ( spl7_57
    | spl7_58
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f860,f527,f869,f865])).

fof(f860,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5(sK3,sK4,sK2))
        | r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2)) )
    | ~ spl7_42 ),
    inference(resolution,[],[f615,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f615,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK6(X1,sK5(sK3,sK4,sK2)),sK5(sK3,sK4,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl7_42 ),
    inference(resolution,[],[f613,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f775,plain,(
    ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f771])).

fof(f771,plain,
    ( $false
    | ~ spl7_23 ),
    inference(resolution,[],[f308,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,sK4)
        | ~ v3_pre_topc(X3,sK2)
        | ~ m1_connsp_2(X3,sK2,sK3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
        | v1_xboole_0(X3) )
    & m1_connsp_2(sK4,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r1_tarski(X3,X2)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    | v1_xboole_0(X3) )
                & m1_connsp_2(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,sK2)
                  | ~ m1_connsp_2(X3,sK2,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,sK2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK2)
                | ~ m1_connsp_2(X3,sK2,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
                | v1_xboole_0(X3) )
            & m1_connsp_2(X2,sK2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK2)
              | ~ m1_connsp_2(X3,sK2,sK3)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
              | v1_xboole_0(X3) )
          & m1_connsp_2(X2,sK2,sK3)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r1_tarski(X3,X2)
            | ~ v3_pre_topc(X3,sK2)
            | ~ m1_connsp_2(X3,sK2,sK3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
            | v1_xboole_0(X3) )
        & m1_connsp_2(X2,sK2,sK3)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ! [X3] :
          ( ~ r1_tarski(X3,sK4)
          | ~ v3_pre_topc(X3,sK2)
          | ~ m1_connsp_2(X3,sK2,sK3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
          | v1_xboole_0(X3) )
      & m1_connsp_2(sK4,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f308,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl7_23
  <=> ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f583,plain,
    ( ~ spl7_39
    | ~ spl7_40
    | spl7_46 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl7_39
    | ~ spl7_40
    | spl7_46 ),
    inference(resolution,[],[f576,f484])).

fof(f484,plain,
    ( sP0(sK3,sK4,sK2)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f483])).

fof(f483,plain,
    ( spl7_39
  <=> sP0(sK3,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f576,plain,
    ( ~ sP0(sK3,sK4,sK2)
    | ~ spl7_40
    | spl7_46 ),
    inference(resolution,[],[f571,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK5(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( r2_hidden(X1,X3)
          & r1_tarski(X3,X2)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f571,plain,
    ( ~ r2_hidden(sK3,sK5(sK3,sK4,sK2))
    | ~ spl7_40
    | spl7_46 ),
    inference(forward_demodulation,[],[f568,f520])).

fof(f568,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2)))
    | spl7_46 ),
    inference(avatar_component_clause,[],[f566])).

fof(f570,plain,
    ( ~ spl7_41
    | ~ spl7_46
    | ~ spl7_18
    | spl7_43 ),
    inference(avatar_split_clause,[],[f553,f531,f251,f566,f522])).

fof(f522,plain,
    ( spl7_41
  <=> m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f251,plain,
    ( spl7_18
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK2,X1))
        | m1_connsp_2(X1,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f531,plain,
    ( spl7_43
  <=> m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f553,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2)))
    | ~ m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_18
    | spl7_43 ),
    inference(resolution,[],[f533,f390])).

fof(f390,plain,
    ( ! [X3] :
        ( m1_connsp_2(X3,sK2,sK3)
        | ~ r2_hidden(sK3,k1_tops_1(sK2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_18 ),
    inference(resolution,[],[f252,f55])).

fof(f55,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK2))
        | m1_connsp_2(X1,sK2,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f251])).

fof(f533,plain,
    ( ~ m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3)
    | spl7_43 ),
    inference(avatar_component_clause,[],[f531])).

fof(f561,plain,
    ( ~ spl7_39
    | spl7_41 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl7_39
    | spl7_41 ),
    inference(resolution,[],[f555,f484])).

fof(f555,plain,
    ( ~ sP0(sK3,sK4,sK2)
    | spl7_41 ),
    inference(resolution,[],[f524,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f524,plain,
    ( ~ m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_41 ),
    inference(avatar_component_clause,[],[f522])).

fof(f548,plain,
    ( ~ spl7_39
    | spl7_44 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl7_39
    | spl7_44 ),
    inference(resolution,[],[f542,f484])).

fof(f542,plain,
    ( ~ sP0(sK3,sK4,sK2)
    | spl7_44 ),
    inference(resolution,[],[f537,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK5(X0,X1,X2),X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f537,plain,
    ( ~ r1_tarski(sK5(sK3,sK4,sK2),sK4)
    | spl7_44 ),
    inference(avatar_component_clause,[],[f535])).

fof(f535,plain,
    ( spl7_44
  <=> r1_tarski(sK5(sK3,sK4,sK2),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f538,plain,
    ( spl7_42
    | ~ spl7_41
    | ~ spl7_43
    | ~ spl7_44
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f516,f483,f535,f531,f522,f527])).

fof(f516,plain,
    ( ~ r1_tarski(sK5(sK3,sK4,sK2),sK4)
    | ~ m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3)
    | ~ m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(sK5(sK3,sK4,sK2))
    | ~ spl7_39 ),
    inference(resolution,[],[f511,f58])).

fof(f58,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK2)
      | ~ r1_tarski(X3,sK4)
      | ~ m1_connsp_2(X3,sK2,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
      | v1_xboole_0(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f511,plain,
    ( v3_pre_topc(sK5(sK3,sK4,sK2),sK2)
    | ~ spl7_39 ),
    inference(resolution,[],[f484,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | v3_pre_topc(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f525,plain,
    ( spl7_40
    | ~ spl7_41
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f515,f483,f88,f522,f518])).

fof(f88,plain,
    ( spl7_2
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f515,plain,
    ( ~ m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2))
    | ~ spl7_2
    | ~ spl7_39 ),
    inference(resolution,[],[f511,f111])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | k1_tops_1(sK2,X0) = X0 )
    | ~ spl7_2 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,
    ( ! [X3,X1] :
        ( ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f509,plain,
    ( ~ spl7_14
    | ~ spl7_35
    | ~ spl7_4
    | spl7_39 ),
    inference(avatar_split_clause,[],[f496,f483,f97,f460,f185])).

fof(f185,plain,
    ( spl7_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f460,plain,
    ( spl7_35
  <=> r2_hidden(sK3,k1_tops_1(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f97,plain,
    ( spl7_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | sP1(sK2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f496,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_4
    | spl7_39 ),
    inference(resolution,[],[f485,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( sP0(X1,X0,sK2)
        | ~ r2_hidden(X1,k1_tops_1(sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_tops_1(X0,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X2,k1_tops_1(X0,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X2,k1_tops_1(X0,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X1,k1_tops_1(X0,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f98,plain,
    ( ! [X0,X1] :
        ( sP1(sK2,X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f485,plain,
    ( ~ sP0(sK3,sK4,sK2)
    | spl7_39 ),
    inference(avatar_component_clause,[],[f483])).

fof(f492,plain,(
    spl7_37 ),
    inference(avatar_contradiction_clause,[],[f490])).

fof(f490,plain,
    ( $false
    | spl7_37 ),
    inference(resolution,[],[f476,f57])).

fof(f57,plain,(
    m1_connsp_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f476,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | spl7_37 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl7_37
  <=> m1_connsp_2(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f489,plain,(
    spl7_36 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl7_36 ),
    inference(resolution,[],[f472,f55])).

fof(f472,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_36 ),
    inference(avatar_component_clause,[],[f470])).

fof(f470,plain,
    ( spl7_36
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f477,plain,
    ( ~ spl7_14
    | ~ spl7_36
    | ~ spl7_37
    | ~ spl7_17
    | spl7_35 ),
    inference(avatar_split_clause,[],[f464,f460,f228,f474,f470,f185])).

fof(f228,plain,
    ( spl7_17
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK2,X1)
        | r2_hidden(X1,k1_tops_1(sK2,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f464,plain,
    ( ~ m1_connsp_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl7_17
    | spl7_35 ),
    inference(resolution,[],[f462,f229])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k1_tops_1(sK2,X0))
        | ~ m1_connsp_2(X0,sK2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f228])).

fof(f462,plain,
    ( ~ r2_hidden(sK3,k1_tops_1(sK2,sK4))
    | spl7_35 ),
    inference(avatar_component_clause,[],[f460])).

fof(f309,plain,
    ( ~ spl7_3
    | spl7_23
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f305,f85,f307,f93])).

fof(f93,plain,
    ( spl7_3
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f85,plain,
    ( spl7_1
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f86,f53])).

fof(f53,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,
    ( ! [X2,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f253,plain,
    ( ~ spl7_13
    | ~ spl7_3
    | spl7_18 ),
    inference(avatar_split_clause,[],[f249,f251,f93,f163])).

fof(f163,plain,
    ( spl7_13
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f249,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tops_1(sK2,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | m1_connsp_2(X1,sK2,X0) ) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f230,plain,
    ( ~ spl7_13
    | ~ spl7_3
    | spl7_17 ),
    inference(avatar_split_clause,[],[f226,f228,f93,f163])).

fof(f226,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK2,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK2))
      | ~ l1_pre_topc(sK2)
      | ~ v2_pre_topc(sK2)
      | r2_hidden(X1,k1_tops_1(sK2,X0)) ) ),
    inference(resolution,[],[f59,f52])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f192,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl7_14 ),
    inference(resolution,[],[f187,f56])).

fof(f187,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f168,plain,(
    spl7_13 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl7_13 ),
    inference(resolution,[],[f165,f53])).

fof(f165,plain,
    ( ~ v2_pre_topc(sK2)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f101,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl7_3 ),
    inference(resolution,[],[f95,f54])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK2)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f99,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f91,f97,f93])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_pre_topc(sK2)
      | sP1(sK2,X0,X1) ) ),
    inference(resolution,[],[f71,f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X0,X2,X1)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f23,f34,f33])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f90,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f62,f88,f85])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (9308)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.50  % (9299)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (9290)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (9305)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (9294)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (9297)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (9292)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (9295)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (9287)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9316)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (9291)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (9299)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f892,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f90,f99,f101,f168,f192,f230,f253,f309,f477,f489,f492,f509,f525,f538,f548,f561,f570,f583,f775,f871,f884,f891])).
% 0.21/0.55  fof(f891,plain,(
% 0.21/0.55    ~spl7_40 | ~spl7_46 | ~spl7_58),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f890])).
% 0.21/0.55  fof(f890,plain,(
% 0.21/0.55    $false | (~spl7_40 | ~spl7_46 | ~spl7_58)),
% 0.21/0.55    inference(resolution,[],[f870,f584])).
% 0.21/0.55  fof(f584,plain,(
% 0.21/0.55    r2_hidden(sK3,sK5(sK3,sK4,sK2)) | (~spl7_40 | ~spl7_46)),
% 0.21/0.55    inference(forward_demodulation,[],[f567,f520])).
% 0.21/0.55  fof(f520,plain,(
% 0.21/0.55    sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2)) | ~spl7_40),
% 0.21/0.55    inference(avatar_component_clause,[],[f518])).
% 0.21/0.55  fof(f518,plain,(
% 0.21/0.55    spl7_40 <=> sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.55  fof(f567,plain,(
% 0.21/0.55    r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2))) | ~spl7_46),
% 0.21/0.55    inference(avatar_component_clause,[],[f566])).
% 0.21/0.55  fof(f566,plain,(
% 0.21/0.55    spl7_46 <=> r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 0.21/0.55  fof(f870,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK5(sK3,sK4,sK2))) ) | ~spl7_58),
% 0.21/0.55    inference(avatar_component_clause,[],[f869])).
% 0.21/0.55  fof(f869,plain,(
% 0.21/0.55    spl7_58 <=> ! [X0] : ~r2_hidden(X0,sK5(sK3,sK4,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).
% 0.21/0.55  fof(f884,plain,(
% 0.21/0.55    ~spl7_40 | ~spl7_42 | ~spl7_46 | ~spl7_57),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f883])).
% 0.21/0.55  fof(f883,plain,(
% 0.21/0.55    $false | (~spl7_40 | ~spl7_42 | ~spl7_46 | ~spl7_57)),
% 0.21/0.55    inference(resolution,[],[f877,f584])).
% 0.21/0.55  fof(f877,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK5(sK3,sK4,sK2))) ) | (~spl7_42 | ~spl7_57)),
% 0.21/0.55    inference(resolution,[],[f867,f613])).
% 0.21/0.55  fof(f613,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X1,sK5(sK3,sK4,sK2)) | ~r2_hidden(X0,X1)) ) | ~spl7_42),
% 0.21/0.55    inference(resolution,[],[f585,f79])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.55    inference(nnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.55  fof(f585,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK5(sK3,sK4,sK2))) | ~r2_hidden(X1,X0)) ) | ~spl7_42),
% 0.21/0.55    inference(resolution,[],[f529,f81])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.55  fof(f529,plain,(
% 0.21/0.55    v1_xboole_0(sK5(sK3,sK4,sK2)) | ~spl7_42),
% 0.21/0.55    inference(avatar_component_clause,[],[f527])).
% 0.21/0.55  fof(f527,plain,(
% 0.21/0.55    spl7_42 <=> v1_xboole_0(sK5(sK3,sK4,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.21/0.55  fof(f867,plain,(
% 0.21/0.55    r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2)) | ~spl7_57),
% 0.21/0.55    inference(avatar_component_clause,[],[f865])).
% 0.21/0.55  % (9288)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f865,plain,(
% 0.21/0.55    spl7_57 <=> r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 0.21/0.55  fof(f871,plain,(
% 0.21/0.55    spl7_57 | spl7_58 | ~spl7_42),
% 0.21/0.55    inference(avatar_split_clause,[],[f860,f527,f869,f865])).
% 0.21/0.55  fof(f860,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK5(sK3,sK4,sK2)) | r1_tarski(sK5(sK3,sK4,sK2),sK5(sK3,sK4,sK2))) ) | ~spl7_42),
% 0.21/0.55    inference(resolution,[],[f615,f76])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(rectify,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f615,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(sK6(X1,sK5(sK3,sK4,sK2)),sK5(sK3,sK4,sK2)) | ~r2_hidden(X0,X1)) ) | ~spl7_42),
% 0.21/0.55    inference(resolution,[],[f613,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f50])).
% 0.21/0.55  fof(f775,plain,(
% 0.21/0.55    ~spl7_23),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f771])).
% 0.21/0.55  fof(f771,plain,(
% 0.21/0.55    $false | ~spl7_23),
% 0.21/0.55    inference(resolution,[],[f308,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ((! [X3] : (~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f15,f38,f37,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(X2,sK2,sK3) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))) => (! [X3] : (~r1_tarski(X3,sK4) | ~v3_pre_topc(X3,sK2) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) & m1_connsp_2(sK4,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.55    inference(negated_conjecture,[],[f12])).
% 0.21/0.55  fof(f12,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.55  fof(f308,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f307])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    spl7_23 <=> ! [X0] : ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.55  fof(f583,plain,(
% 0.21/0.55    ~spl7_39 | ~spl7_40 | spl7_46),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f580])).
% 0.21/0.55  fof(f580,plain,(
% 0.21/0.55    $false | (~spl7_39 | ~spl7_40 | spl7_46)),
% 0.21/0.55    inference(resolution,[],[f576,f484])).
% 0.21/0.55  fof(f484,plain,(
% 0.21/0.55    sP0(sK3,sK4,sK2) | ~spl7_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f483])).
% 0.21/0.55  fof(f483,plain,(
% 0.21/0.55    spl7_39 <=> sP0(sK3,sK4,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.55  fof(f576,plain,(
% 0.21/0.55    ~sP0(sK3,sK4,sK2) | (~spl7_40 | spl7_46)),
% 0.21/0.55    inference(resolution,[],[f571,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,sK5(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & ((r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f44,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) => (r2_hidden(X0,sK5(X0,X1,X2)) & r1_tarski(sK5(X0,X1,X2),X1) & v3_pre_topc(sK5(X0,X1,X2),X2) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (~r2_hidden(X0,X3) | ~r1_tarski(X3,X1) | ~v3_pre_topc(X3,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))) & (? [X4] : (r2_hidden(X0,X4) & r1_tarski(X4,X1) & v3_pre_topc(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))) | ~sP0(X0,X1,X2)))),
% 0.21/0.55    inference(rectify,[],[f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X2,X0)))),
% 0.21/0.55    inference(nnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f571,plain,(
% 0.21/0.55    ~r2_hidden(sK3,sK5(sK3,sK4,sK2)) | (~spl7_40 | spl7_46)),
% 0.21/0.55    inference(forward_demodulation,[],[f568,f520])).
% 0.21/0.55  fof(f568,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2))) | spl7_46),
% 0.21/0.55    inference(avatar_component_clause,[],[f566])).
% 0.21/0.55  fof(f570,plain,(
% 0.21/0.55    ~spl7_41 | ~spl7_46 | ~spl7_18 | spl7_43),
% 0.21/0.55    inference(avatar_split_clause,[],[f553,f531,f251,f566,f522])).
% 0.21/0.55  fof(f522,plain,(
% 0.21/0.55    spl7_41 <=> m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    spl7_18 <=> ! [X1,X0] : (~r2_hidden(X0,k1_tops_1(sK2,X1)) | m1_connsp_2(X1,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.55  fof(f531,plain,(
% 0.21/0.55    spl7_43 <=> m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.55  fof(f553,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_tops_1(sK2,sK5(sK3,sK4,sK2))) | ~m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | (~spl7_18 | spl7_43)),
% 0.21/0.55    inference(resolution,[],[f533,f390])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    ( ! [X3] : (m1_connsp_2(X3,sK2,sK3) | ~r2_hidden(sK3,k1_tops_1(sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_18),
% 0.21/0.55    inference(resolution,[],[f252,f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f252,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | m1_connsp_2(X1,sK2,X0) | ~r2_hidden(X0,k1_tops_1(sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_18),
% 0.21/0.55    inference(avatar_component_clause,[],[f251])).
% 0.21/0.55  fof(f533,plain,(
% 0.21/0.55    ~m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3) | spl7_43),
% 0.21/0.55    inference(avatar_component_clause,[],[f531])).
% 0.21/0.55  fof(f561,plain,(
% 0.21/0.55    ~spl7_39 | spl7_41),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f558])).
% 0.21/0.55  fof(f558,plain,(
% 0.21/0.55    $false | (~spl7_39 | spl7_41)),
% 0.21/0.55    inference(resolution,[],[f555,f484])).
% 0.21/0.55  fof(f555,plain,(
% 0.21/0.55    ~sP0(sK3,sK4,sK2) | spl7_41),
% 0.21/0.55    inference(resolution,[],[f524,f66])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f524,plain,(
% 0.21/0.55    ~m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | spl7_41),
% 0.21/0.55    inference(avatar_component_clause,[],[f522])).
% 0.21/0.55  fof(f548,plain,(
% 0.21/0.55    ~spl7_39 | spl7_44),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f545])).
% 0.21/0.55  fof(f545,plain,(
% 0.21/0.55    $false | (~spl7_39 | spl7_44)),
% 0.21/0.55    inference(resolution,[],[f542,f484])).
% 0.21/0.55  fof(f542,plain,(
% 0.21/0.55    ~sP0(sK3,sK4,sK2) | spl7_44),
% 0.21/0.55    inference(resolution,[],[f537,f68])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(sK5(X0,X1,X2),X1) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f537,plain,(
% 0.21/0.55    ~r1_tarski(sK5(sK3,sK4,sK2),sK4) | spl7_44),
% 0.21/0.55    inference(avatar_component_clause,[],[f535])).
% 0.21/0.55  fof(f535,plain,(
% 0.21/0.55    spl7_44 <=> r1_tarski(sK5(sK3,sK4,sK2),sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.55  fof(f538,plain,(
% 0.21/0.55    spl7_42 | ~spl7_41 | ~spl7_43 | ~spl7_44 | ~spl7_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f516,f483,f535,f531,f522,f527])).
% 0.21/0.55  fof(f516,plain,(
% 0.21/0.55    ~r1_tarski(sK5(sK3,sK4,sK2),sK4) | ~m1_connsp_2(sK5(sK3,sK4,sK2),sK2,sK3) | ~m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(sK5(sK3,sK4,sK2)) | ~spl7_39),
% 0.21/0.55    inference(resolution,[],[f511,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X3] : (~v3_pre_topc(X3,sK2) | ~r1_tarski(X3,sK4) | ~m1_connsp_2(X3,sK2,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(X3)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f511,plain,(
% 0.21/0.55    v3_pre_topc(sK5(sK3,sK4,sK2),sK2) | ~spl7_39),
% 0.21/0.55    inference(resolution,[],[f484,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | v3_pre_topc(sK5(X0,X1,X2),X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f525,plain,(
% 0.21/0.55    spl7_40 | ~spl7_41 | ~spl7_2 | ~spl7_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f515,f483,f88,f522,f518])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    spl7_2 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f515,plain,(
% 0.21/0.55    ~m1_subset_1(sK5(sK3,sK4,sK2),k1_zfmisc_1(u1_struct_0(sK2))) | sK5(sK3,sK4,sK2) = k1_tops_1(sK2,sK5(sK3,sK4,sK2)) | (~spl7_2 | ~spl7_39)),
% 0.21/0.55    inference(resolution,[],[f511,f111])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_pre_topc(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k1_tops_1(sK2,X0) = X0) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f89,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    l1_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X3,X1] : (~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1)) ) | ~spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f88])).
% 0.21/0.55  fof(f509,plain,(
% 0.21/0.55    ~spl7_14 | ~spl7_35 | ~spl7_4 | spl7_39),
% 0.21/0.55    inference(avatar_split_clause,[],[f496,f483,f97,f460,f185])).
% 0.21/0.55  fof(f185,plain,(
% 0.21/0.55    spl7_14 <=> m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    spl7_35 <=> r2_hidden(sK3,k1_tops_1(sK2,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.55  fof(f97,plain,(
% 0.21/0.55    spl7_4 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(sK2,X0,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.55  fof(f496,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_tops_1(sK2,sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl7_4 | spl7_39)),
% 0.21/0.55    inference(resolution,[],[f485,f102])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP0(X1,X0,sK2) | ~r2_hidden(X1,k1_tops_1(sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_4),
% 0.21/0.55    inference(resolution,[],[f98,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X2,k1_tops_1(X0,X1)) | sP0(X2,X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r2_hidden(X2,k1_tops_1(X0,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X2,k1_tops_1(X0,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.55    inference(rectify,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X2,X1] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0,X2,X1] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    ( ! [X0,X1] : (sP1(sK2,X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f97])).
% 0.21/0.55  fof(f485,plain,(
% 0.21/0.55    ~sP0(sK3,sK4,sK2) | spl7_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f483])).
% 0.21/0.55  fof(f492,plain,(
% 0.21/0.55    spl7_37),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f490])).
% 0.21/0.55  fof(f490,plain,(
% 0.21/0.55    $false | spl7_37),
% 0.21/0.55    inference(resolution,[],[f476,f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f476,plain,(
% 0.21/0.55    ~m1_connsp_2(sK4,sK2,sK3) | spl7_37),
% 0.21/0.55    inference(avatar_component_clause,[],[f474])).
% 0.21/0.55  fof(f474,plain,(
% 0.21/0.55    spl7_37 <=> m1_connsp_2(sK4,sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.21/0.55  fof(f489,plain,(
% 0.21/0.55    spl7_36),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f487])).
% 0.21/0.55  fof(f487,plain,(
% 0.21/0.55    $false | spl7_36),
% 0.21/0.55    inference(resolution,[],[f472,f55])).
% 0.21/0.55  fof(f472,plain,(
% 0.21/0.55    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl7_36),
% 0.21/0.55    inference(avatar_component_clause,[],[f470])).
% 0.21/0.55  fof(f470,plain,(
% 0.21/0.55    spl7_36 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.21/0.55  fof(f477,plain,(
% 0.21/0.55    ~spl7_14 | ~spl7_36 | ~spl7_37 | ~spl7_17 | spl7_35),
% 0.21/0.55    inference(avatar_split_clause,[],[f464,f460,f228,f474,f470,f185])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    spl7_17 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK2,X1) | r2_hidden(X1,k1_tops_1(sK2,X0)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.55  fof(f464,plain,(
% 0.21/0.55    ~m1_connsp_2(sK4,sK2,sK3) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | (~spl7_17 | spl7_35)),
% 0.21/0.55    inference(resolution,[],[f462,f229])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(X1,k1_tops_1(sK2,X0)) | ~m1_connsp_2(X0,sK2,X1) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl7_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f228])).
% 0.21/0.55  fof(f462,plain,(
% 0.21/0.55    ~r2_hidden(sK3,k1_tops_1(sK2,sK4)) | spl7_35),
% 0.21/0.55    inference(avatar_component_clause,[],[f460])).
% 0.21/0.55  fof(f309,plain,(
% 0.21/0.55    ~spl7_3 | spl7_23 | ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f305,f85,f307,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    spl7_3 <=> l1_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    spl7_1 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2)) ) | ~spl7_1),
% 0.21/0.55    inference(resolution,[],[f86,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    v2_pre_topc(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    ( ! [X2,X0] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f85])).
% 0.21/0.55  fof(f253,plain,(
% 0.21/0.55    ~spl7_13 | ~spl7_3 | spl7_18),
% 0.21/0.55    inference(avatar_split_clause,[],[f249,f251,f93,f163])).
% 0.21/0.55  fof(f163,plain,(
% 0.21/0.55    spl7_13 <=> v2_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | m1_connsp_2(X1,sK2,X0)) )),
% 0.21/0.55    inference(resolution,[],[f60,f52])).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ~v2_struct_0(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f39])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    ~spl7_13 | ~spl7_3 | spl7_17),
% 0.21/0.55    inference(avatar_split_clause,[],[f226,f228,f93,f163])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_connsp_2(X0,sK2,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | r2_hidden(X1,k1_tops_1(sK2,X0))) )),
% 0.21/0.55    inference(resolution,[],[f59,f52])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f40])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl7_14),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f189])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    $false | spl7_14),
% 0.21/0.55    inference(resolution,[],[f187,f56])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) | spl7_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f185])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    spl7_13),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f167])).
% 0.21/0.55  fof(f167,plain,(
% 0.21/0.55    $false | spl7_13),
% 0.21/0.55    inference(resolution,[],[f165,f53])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    ~v2_pre_topc(sK2) | spl7_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f163])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl7_3),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    $false | spl7_3),
% 0.21/0.55    inference(resolution,[],[f95,f54])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ~l1_pre_topc(sK2) | spl7_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f93])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    ~spl7_3 | spl7_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f91,f97,f93])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK2) | sP1(sK2,X0,X1)) )),
% 0.21/0.55    inference(resolution,[],[f71,f53])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sP1(X0,X2,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(definition_folding,[],[f23,f34,f33])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    spl7_1 | spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f62,f88,f85])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (9299)------------------------------
% 0.21/0.55  % (9299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9299)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (9299)Memory used [KB]: 6652
% 0.21/0.55  % (9299)Time elapsed: 0.123 s
% 0.21/0.55  % (9299)------------------------------
% 0.21/0.55  % (9299)------------------------------
% 0.21/0.55  % (9286)Success in time 0.199 s
%------------------------------------------------------------------------------
