%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1711+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:23 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 839 expanded)
%              Number of leaves         :   56 ( 472 expanded)
%              Depth                    :   13
%              Number of atoms          : 1123 (6511 expanded)
%              Number of equality atoms :   40 ( 526 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (17458)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% (17475)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% (17465)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% (17471)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% (17473)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (17467)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f732,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f144,f150,f156,f162,f169,f174,f181,f186,f198,f204,f219,f220,f230,f235,f240,f250,f255,f260,f316,f335,f340,f345,f350,f644,f665])).

fof(f665,plain,
    ( spl10_94
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(avatar_split_clause,[],[f664,f332,f313,f641])).

fof(f641,plain,
    ( spl10_94
  <=> r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f313,plain,
    ( spl10_41
  <=> r1_tarski(k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f332,plain,
    ( spl10_43
  <=> r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_43])])).

fof(f664,plain,
    ( r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7))
    | ~ spl10_41
    | ~ spl10_43 ),
    inference(unit_resulting_resolution,[],[f315,f334,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f334,plain,
    ( r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)))
    | ~ spl10_43 ),
    inference(avatar_component_clause,[],[f332])).

fof(f315,plain,
    ( r1_tarski(k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f313])).

fof(f644,plain,
    ( ~ spl10_46
    | ~ spl10_45
    | ~ spl10_94
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f636,f337,f641,f342,f347])).

fof(f347,plain,
    ( spl10_46
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f342,plain,
    ( spl10_45
  <=> v3_pre_topc(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_45])])).

fof(f337,plain,
    ( spl10_44
  <=> r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f636,plain,
    ( ~ r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7))
    | ~ v3_pre_topc(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl10_44 ),
    inference(resolution,[],[f339,f54])).

fof(f54,plain,(
    ! [X8] :
      ( ~ r2_hidden(sK3,X8)
      | ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
        | ~ r2_hidden(sK3,X8)
        | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
    & m1_connsp_2(sK7,sK2,sK5)
    & m1_connsp_2(sK6,sK1,sK4)
    & sK3 = sK5
    & sK3 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f11,f32,f31,f30,f29,f28,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ? [X7] :
                                    ( ! [X8] :
                                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                        | ~ r2_hidden(X3,X8)
                                        | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                    & m1_connsp_2(X7,X2,X5) )
                                & m1_connsp_2(X6,X1,X4) )
                            & X3 = X5
                            & X3 = X4
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)))) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ? [X7] :
                                ( ! [X8] :
                                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                    | ~ r2_hidden(X3,X8)
                                    | ~ v3_pre_topc(X8,k1_tsep_1(sK0,X1,X2))
                                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,X1,X2)))) )
                                & m1_connsp_2(X7,X2,X5) )
                            & m1_connsp_2(X6,X1,X4) )
                        & X3 = X5
                        & X3 = X4
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,X1,X2))) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ? [X7] :
                              ( ! [X8] :
                                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                  | ~ r2_hidden(X3,X8)
                                  | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,X2))
                                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) )
                              & m1_connsp_2(X7,X2,X5) )
                          & m1_connsp_2(X6,sK1,X4) )
                      & X3 = X5
                      & X3 = X4
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ? [X7] :
                            ( ! [X8] :
                                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                | ~ r2_hidden(X3,X8)
                                | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,X2))
                                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,X2)))) )
                            & m1_connsp_2(X7,X2,X5) )
                        & m1_connsp_2(X6,sK1,X4) )
                    & X3 = X5
                    & X3 = X4
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,X2))) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ? [X7] :
                          ( ! [X8] :
                              ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                              | ~ r2_hidden(X3,X8)
                              | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                          & m1_connsp_2(X7,sK2,X5) )
                      & m1_connsp_2(X6,sK1,X4) )
                  & X3 = X5
                  & X3 = X4
                  & m1_subset_1(X5,u1_struct_0(sK2)) )
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ? [X7] :
                        ( ! [X8] :
                            ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                            | ~ r2_hidden(X3,X8)
                            | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                        & m1_connsp_2(X7,sK2,X5) )
                    & m1_connsp_2(X6,sK1,X4) )
                & X3 = X5
                & X3 = X4
                & m1_subset_1(X5,u1_struct_0(sK2)) )
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ! [X8] :
                          ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                          | ~ r2_hidden(sK3,X8)
                          | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                          | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                      & m1_connsp_2(X7,sK2,X5) )
                  & m1_connsp_2(X6,sK1,X4) )
              & sK3 = X5
              & sK3 = X4
              & m1_subset_1(X5,u1_struct_0(sK2)) )
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ! [X8] :
                        ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                        | ~ r2_hidden(sK3,X8)
                        | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                    & m1_connsp_2(X7,sK2,X5) )
                & m1_connsp_2(X6,sK1,X4) )
            & sK3 = X5
            & sK3 = X4
            & m1_subset_1(X5,u1_struct_0(sK2)) )
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ! [X8] :
                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                      | ~ r2_hidden(sK3,X8)
                      | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                  & m1_connsp_2(X7,sK2,X5) )
              & m1_connsp_2(X6,sK1,sK4) )
          & sK3 = X5
          & sK3 = sK4
          & m1_subset_1(X5,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ! [X8] :
                    ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                    | ~ r2_hidden(sK3,X8)
                    | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
                & m1_connsp_2(X7,sK2,X5) )
            & m1_connsp_2(X6,sK1,sK4) )
        & sK3 = X5
        & sK3 = sK4
        & m1_subset_1(X5,u1_struct_0(sK2)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ! [X8] :
                  ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                  | ~ r2_hidden(sK3,X8)
                  | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                  | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
              & m1_connsp_2(X7,sK2,sK5) )
          & m1_connsp_2(X6,sK1,sK4) )
      & sK3 = sK5
      & sK3 = sK4
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ! [X8] :
                ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                | ~ r2_hidden(sK3,X8)
                | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
                | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
            & m1_connsp_2(X7,sK2,sK5) )
        & m1_connsp_2(X6,sK1,sK4) )
   => ( ? [X7] :
          ( ! [X8] :
              ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
              | ~ r2_hidden(sK3,X8)
              | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
              | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
          & m1_connsp_2(X7,sK2,sK5) )
      & m1_connsp_2(sK6,sK1,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X7] :
        ( ! [X8] :
            ( ~ r1_tarski(X8,k2_xboole_0(sK6,X7))
            | ~ r2_hidden(sK3,X8)
            | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
            | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
        & m1_connsp_2(X7,sK2,sK5) )
   => ( ! [X8] :
          ( ~ r1_tarski(X8,k2_xboole_0(sK6,sK7))
          | ~ r2_hidden(sK3,X8)
          | ~ v3_pre_topc(X8,k1_tsep_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) )
      & m1_connsp_2(sK7,sK2,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( ! [X8] :
                                      ( ~ r1_tarski(X8,k2_xboole_0(X6,X7))
                                      | ~ r2_hidden(X3,X8)
                                      | ~ v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                                  & m1_connsp_2(X7,X2,X5) )
                              & m1_connsp_2(X6,X1,X4) )
                          & X3 = X5
                          & X3 = X4
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ( ( X3 = X5
                                & X3 = X4 )
                             => ! [X6] :
                                  ( m1_connsp_2(X6,X1,X4)
                                 => ! [X7] :
                                      ( m1_connsp_2(X7,X2,X5)
                                     => ? [X8] :
                                          ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                          & r2_hidden(X3,X8)
                                          & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                          & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ( ( X3 = X5
                              & X3 = X4 )
                           => ! [X6] :
                                ( m1_connsp_2(X6,X1,X4)
                               => ! [X7] :
                                    ( m1_connsp_2(X7,X2,X5)
                                   => ? [X8] :
                                        ( r1_tarski(X8,k2_xboole_0(X6,X7))
                                        & r2_hidden(X3,X8)
                                        & v3_pre_topc(X8,k1_tsep_1(X0,X1,X2))
                                        & m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).

fof(f339,plain,
    ( r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)))
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f337])).

fof(f350,plain,
    ( spl10_46
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f325,f257,f252,f237,f232,f215,f210,f135,f130,f125,f120,f115,f110,f105,f100,f347])).

fof(f100,plain,
    ( spl10_7
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f105,plain,
    ( spl10_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f110,plain,
    ( spl10_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f115,plain,
    ( spl10_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f120,plain,
    ( spl10_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f125,plain,
    ( spl10_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f130,plain,
    ( spl10_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f135,plain,
    ( spl10_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f210,plain,
    ( spl10_25
  <=> r2_hidden(sK3,sK9(sK2,sK3,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f215,plain,
    ( spl10_26
  <=> r2_hidden(sK3,sK9(sK1,sK3,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f232,plain,
    ( spl10_28
  <=> v3_pre_topc(sK9(sK1,sK3,sK6),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f237,plain,
    ( spl10_29
  <=> m1_subset_1(sK9(sK1,sK3,sK6),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_29])])).

fof(f252,plain,
    ( spl10_31
  <=> v3_pre_topc(sK9(sK2,sK3,sK7),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f257,plain,
    ( spl10_32
  <=> m1_subset_1(sK9(sK2,sK3,sK7),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f325,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f117,f107,f234,f217,f239,f102,f212,f254,f259,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X3,X5)
      | m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r1_tarski(sK8(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
                            & r2_hidden(X3,sK8(X0,X1,X2,X3,X4,X5))
                            & v3_pre_topc(sK8(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
                            & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f17,f34])).

fof(f34,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_tarski(X6,k2_xboole_0(X4,X5))
          & r2_hidden(X3,X6)
          & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
          & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
     => ( r1_tarski(sK8(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
        & r2_hidden(X3,sK8(X0,X1,X2,X3,X4,X5))
        & v3_pre_topc(sK8(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
        & m1_subset_1(sK8(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ? [X6] :
                              ( r1_tarski(X6,k2_xboole_0(X4,X5))
                              & r2_hidden(X3,X6)
                              & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2))
                              & m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)))) )
                          | ~ r2_hidden(X3,X5)
                          | ~ v3_pre_topc(X5,X2)
                          | ~ r2_hidden(X3,X4)
                          | ~ v3_pre_topc(X4,X1)
                          | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                         => ~ ( ! [X6] :
                                  ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2))))
                                 => ~ ( r1_tarski(X6,k2_xboole_0(X4,X5))
                                      & r2_hidden(X3,X6)
                                      & v3_pre_topc(X6,k1_tsep_1(X0,X1,X2)) ) )
                              & r2_hidden(X3,X5)
                              & v3_pre_topc(X5,X2)
                              & r2_hidden(X3,X4)
                              & v3_pre_topc(X4,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tmap_1)).

fof(f259,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f257])).

fof(f254,plain,
    ( v3_pre_topc(sK9(sK2,sK3,sK7),sK2)
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f252])).

fof(f212,plain,
    ( r2_hidden(sK3,sK9(sK2,sK3,sK7))
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f102,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f239,plain,
    ( m1_subset_1(sK9(sK1,sK3,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_29 ),
    inference(avatar_component_clause,[],[f237])).

fof(f217,plain,
    ( r2_hidden(sK3,sK9(sK1,sK3,sK6))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f215])).

fof(f234,plain,
    ( v3_pre_topc(sK9(sK1,sK3,sK6),sK1)
    | ~ spl10_28 ),
    inference(avatar_component_clause,[],[f232])).

fof(f107,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f117,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f112,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f122,plain,
    ( ~ v2_struct_0(sK1)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f120])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f130])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f345,plain,
    ( spl10_45
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f326,f257,f252,f237,f232,f215,f210,f135,f130,f125,f120,f115,f110,f105,f100,f342])).

fof(f326,plain,
    ( v3_pre_topc(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f117,f107,f234,f217,f239,f102,f212,f254,f259,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v3_pre_topc(sK8(X0,X1,X2,X3,X4,X5),k1_tsep_1(X0,X1,X2))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f340,plain,
    ( spl10_44
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f327,f257,f252,f237,f232,f215,f210,f135,f130,f125,f120,f115,f110,f105,f100,f337])).

fof(f327,plain,
    ( r2_hidden(sK3,sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)))
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f117,f107,f234,f217,f239,f102,f212,f254,f259,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X3,X5)
      | r2_hidden(X3,sK8(X0,X1,X2,X3,X4,X5))
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f335,plain,
    ( spl10_43
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(avatar_split_clause,[],[f328,f257,f252,f237,f232,f215,f210,f135,f130,f125,f120,f115,f110,f105,f100,f332])).

fof(f328,plain,
    ( r1_tarski(sK8(sK0,sK1,sK2,sK3,sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)))
    | ~ spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14
    | ~ spl10_25
    | ~ spl10_26
    | ~ spl10_28
    | ~ spl10_29
    | ~ spl10_31
    | ~ spl10_32 ),
    inference(unit_resulting_resolution,[],[f137,f132,f127,f122,f112,f117,f107,f234,f217,f239,f102,f212,f254,f259,f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tarski(sK8(X0,X1,X2,X3,X4,X5),k2_xboole_0(X4,X5))
      | ~ r2_hidden(X3,X5)
      | ~ v3_pre_topc(X5,X2)
      | ~ r2_hidden(X3,X4)
      | ~ v3_pre_topc(X4,X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f316,plain,
    ( spl10_41
    | ~ spl10_27
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f305,f247,f227,f313])).

fof(f227,plain,
    ( spl10_27
  <=> r1_tarski(sK9(sK1,sK3,sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f247,plain,
    ( spl10_30
  <=> r1_tarski(sK9(sK2,sK3,sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f305,plain,
    ( r1_tarski(k2_xboole_0(sK9(sK1,sK3,sK6),sK9(sK2,sK3,sK7)),k2_xboole_0(sK6,sK7))
    | ~ spl10_27
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f229,f249,f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f249,plain,
    ( r1_tarski(sK9(sK2,sK3,sK7),sK7)
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f247])).

fof(f229,plain,
    ( r1_tarski(sK9(sK1,sK3,sK6),sK6)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f227])).

fof(f260,plain,
    ( spl10_32
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f241,f201,f183,f171,f159,f147,f110,f257])).

fof(f147,plain,
    ( spl10_16
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f159,plain,
    ( spl10_18
  <=> m1_connsp_2(sK7,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f171,plain,
    ( spl10_20
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f183,plain,
    ( spl10_22
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f201,plain,
    ( spl10_24
  <=> m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f241,plain,
    ( m1_subset_1(sK9(sK2,sK3,sK7),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f112,f185,f173,f149,f161,f203,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( r2_hidden(X1,sK9(X0,X1,X2))
                    & r1_tarski(sK9(X0,X1,X2),X2)
                    & v3_pre_topc(sK9(X0,X1,X2),X0)
                    & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK9(X0,X1,X2))
        & r1_tarski(sK9(X0,X1,X2),X2)
        & v3_pre_topc(sK9(X0,X1,X2),X0)
        & m1_subset_1(sK9(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ! [X3] :
                      ( ~ r2_hidden(X1,X3)
                      | ~ r1_tarski(X3,X2)
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( r2_hidden(X1,X4)
                      & r1_tarski(X4,X2)
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
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
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> ? [X3] :
                    ( r2_hidden(X1,X3)
                    & r1_tarski(X3,X2)
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_connsp_2)).

fof(f203,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f201])).

fof(f161,plain,
    ( m1_connsp_2(sK7,sK2,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f159])).

fof(f149,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f147])).

fof(f173,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f185,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f255,plain,
    ( spl10_31
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f242,f201,f183,f171,f159,f147,f110,f252])).

fof(f242,plain,
    ( v3_pre_topc(sK9(sK2,sK3,sK7),sK2)
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f112,f185,f173,f149,f161,f203,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK9(X0,X1,X2),X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f250,plain,
    ( spl10_30
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(avatar_split_clause,[],[f243,f201,f183,f171,f159,f147,f110,f247])).

fof(f243,plain,
    ( r1_tarski(sK9(sK2,sK3,sK7),sK7)
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22
    | ~ spl10_24 ),
    inference(unit_resulting_resolution,[],[f112,f185,f173,f149,f161,f203,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK9(X0,X1,X2),X2)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f240,plain,
    ( spl10_29
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f221,f195,f178,f166,f153,f141,f120,f237])).

fof(f141,plain,
    ( spl10_15
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f153,plain,
    ( spl10_17
  <=> m1_connsp_2(sK6,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f166,plain,
    ( spl10_19
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f178,plain,
    ( spl10_21
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f195,plain,
    ( spl10_23
  <=> m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f221,plain,
    ( m1_subset_1(sK9(sK1,sK3,sK6),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f122,f180,f168,f143,f155,f197,f61])).

fof(f197,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f155,plain,
    ( m1_connsp_2(sK6,sK1,sK3)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f143,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f168,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f180,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f235,plain,
    ( spl10_28
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f222,f195,f178,f166,f153,f141,f120,f232])).

fof(f222,plain,
    ( v3_pre_topc(sK9(sK1,sK3,sK6),sK1)
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f122,f180,f168,f143,f155,f197,f62])).

fof(f230,plain,
    ( spl10_27
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(avatar_split_clause,[],[f223,f195,f178,f166,f153,f141,f120,f227])).

fof(f223,plain,
    ( r1_tarski(sK9(sK1,sK3,sK6),sK6)
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21
    | ~ spl10_23 ),
    inference(unit_resulting_resolution,[],[f122,f180,f168,f143,f155,f197,f63])).

fof(f220,plain,
    ( spl10_9
    | ~ spl10_22
    | ~ spl10_20
    | ~ spl10_16
    | spl10_25
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f208,f159,f210,f147,f171,f183,f110])).

fof(f208,plain,
    ( r2_hidden(sK3,sK9(sK2,sK3,sK7))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | v2_struct_0(sK2)
    | ~ spl10_18 ),
    inference(resolution,[],[f190,f161])).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,sK9(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,sK9(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(condensation,[],[f188])).

fof(f188,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,sK9(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X0,X1,X2)
      | r2_hidden(X2,sK9(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_connsp_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f64,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,sK9(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f219,plain,
    ( spl10_11
    | ~ spl10_21
    | ~ spl10_19
    | ~ spl10_15
    | spl10_26
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f207,f153,f215,f141,f166,f178,f120])).

fof(f207,plain,
    ( r2_hidden(sK3,sK9(sK1,sK3,sK6))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl10_17 ),
    inference(resolution,[],[f190,f155])).

fof(f204,plain,
    ( spl10_24
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f199,f183,f171,f159,f147,f110,f201])).

fof(f199,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK2)))
    | spl10_9
    | ~ spl10_16
    | ~ spl10_18
    | ~ spl10_20
    | ~ spl10_22 ),
    inference(unit_resulting_resolution,[],[f112,f173,f161,f149,f185,f66])).

fof(f198,plain,
    ( spl10_23
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f193,f178,f166,f153,f141,f120,f195])).

fof(f193,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK1)))
    | spl10_11
    | ~ spl10_15
    | ~ spl10_17
    | ~ spl10_19
    | ~ spl10_21 ),
    inference(unit_resulting_resolution,[],[f122,f168,f155,f143,f180,f66])).

fof(f186,plain,
    ( spl10_22
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f175,f130,f125,f105,f183])).

fof(f175,plain,
    ( v2_pre_topc(sK2)
    | ~ spl10_8
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f132,f127,f107,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f181,plain,
    ( spl10_21
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f176,f130,f125,f115,f178])).

fof(f176,plain,
    ( v2_pre_topc(sK1)
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_13 ),
    inference(unit_resulting_resolution,[],[f132,f127,f117,f67])).

fof(f174,plain,
    ( spl10_20
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f163,f125,f105,f171])).

fof(f163,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f127,f107,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f169,plain,
    ( spl10_19
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f164,f125,f115,f166])).

fof(f164,plain,
    ( l1_pre_topc(sK1)
    | ~ spl10_10
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f127,f117,f68])).

fof(f162,plain,
    ( spl10_18
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f157,f80,f70,f159])).

fof(f70,plain,
    ( spl10_1
  <=> m1_connsp_2(sK7,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f80,plain,
    ( spl10_3
  <=> sK3 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f157,plain,
    ( m1_connsp_2(sK7,sK2,sK3)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f72,f82])).

fof(f82,plain,
    ( sK3 = sK5
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f72,plain,
    ( m1_connsp_2(sK7,sK2,sK5)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f156,plain,
    ( spl10_17
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f151,f85,f75,f153])).

fof(f75,plain,
    ( spl10_2
  <=> m1_connsp_2(sK6,sK1,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f85,plain,
    ( spl10_4
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f151,plain,
    ( m1_connsp_2(sK6,sK1,sK3)
    | ~ spl10_2
    | ~ spl10_4 ),
    inference(forward_demodulation,[],[f77,f87])).

fof(f87,plain,
    ( sK3 = sK4
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f77,plain,
    ( m1_connsp_2(sK6,sK1,sK4)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f150,plain,
    ( spl10_16
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f145,f90,f80,f147])).

fof(f90,plain,
    ( spl10_5
  <=> m1_subset_1(sK5,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f145,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl10_3
    | ~ spl10_5 ),
    inference(backward_demodulation,[],[f92,f82])).

fof(f92,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f144,plain,
    ( spl10_15
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f139,f95,f85,f141])).

fof(f95,plain,
    ( spl10_6
  <=> m1_subset_1(sK4,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f139,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl10_4
    | ~ spl10_6 ),
    inference(backward_demodulation,[],[f97,f87])).

fof(f97,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f138,plain,(
    ~ spl10_14 ),
    inference(avatar_split_clause,[],[f40,f135])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f133,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f41,f130])).

fof(f41,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f42,f125])).

fof(f42,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f123,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f43,f120])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f118,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f44,f115])).

fof(f44,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f113,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f45,f110])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f46,f105])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f103,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f47,f100])).

fof(f47,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f48,f95])).

fof(f48,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f49,f90])).

fof(f49,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f50,f85])).

fof(f50,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f51,f80])).

fof(f51,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f52,f75])).

fof(f52,plain,(
    m1_connsp_2(sK6,sK1,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f53,f70])).

fof(f53,plain,(
    m1_connsp_2(sK7,sK2,sK5) ),
    inference(cnf_transformation,[],[f33])).

%------------------------------------------------------------------------------
