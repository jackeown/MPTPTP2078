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
% DateTime   : Thu Dec  3 13:13:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 239 expanded)
%              Number of leaves         :   29 ( 108 expanded)
%              Depth                    :   10
%              Number of atoms          :  483 (1277 expanded)
%              Number of equality atoms :   28 ( 111 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f191,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f81,f86,f91,f112,f123,f134,f141,f157,f168,f187,f190])).

fof(f190,plain,
    ( ~ spl6_13
    | ~ spl6_9
    | spl6_8
    | spl6_21 ),
    inference(avatar_split_clause,[],[f188,f185,f84,f89,f129])).

fof(f129,plain,
    ( spl6_13
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f89,plain,
    ( spl6_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f84,plain,
    ( spl6_8
  <=> v1_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f185,plain,
    ( spl6_21
  <=> r2_hidden(sK4(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f188,plain,
    ( v1_tops_2(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | spl6_21 ),
    inference(resolution,[],[f186,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK4(X0,X1),X0)
                & r2_hidden(sK4(X0,X1),X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).

fof(f186,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( ~ spl6_21
    | ~ spl6_6
    | spl6_18 ),
    inference(avatar_split_clause,[],[f182,f164,f75,f185])).

fof(f75,plain,
    ( spl6_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f164,plain,
    ( spl6_18
  <=> r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f182,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl6_6
    | spl6_18 ),
    inference(resolution,[],[f170,f76])).

fof(f76,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK4(sK2,sK1),X0) )
    | spl6_18 ),
    inference(resolution,[],[f165,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f165,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f168,plain,
    ( ~ spl6_13
    | ~ spl6_18
    | spl6_8
    | ~ spl6_9
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f162,f155,f89,f84,f164,f129])).

fof(f155,plain,
    ( spl6_17
  <=> ! [X0] :
        ( v1_tops_2(X0,sK2)
        | ~ r1_tarski(sK4(sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r2_hidden(sK4(sK2,X0),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f162,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(sK1,sK2)
    | ~ r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK2)
    | ~ spl6_17 ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | v1_tops_2(sK1,sK2)
    | ~ r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_2(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | ~ spl6_17 ),
    inference(resolution,[],[f158,f42])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_17 ),
    inference(resolution,[],[f156,f53])).

fof(f53,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f156,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(sK2,X0),u1_struct_0(sK0))
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r2_hidden(sK4(sK2,X0),sK1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( ~ spl6_13
    | spl6_17
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f153,f132,f155,f129])).

fof(f132,plain,
    ( spl6_14
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f153,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r1_tarski(sK4(sK2,X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK2) )
    | ~ spl6_14 ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,
    ( ! [X0] :
        ( v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r1_tarski(sK4(sK2,X0),u1_struct_0(sK0))
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl6_14 ),
    inference(resolution,[],[f150,f41])).

% (28389)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
        | v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ r1_tarski(sK4(sK2,X0),u1_struct_0(sK0)) )
    | ~ spl6_14 ),
    inference(resolution,[],[f133,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | v1_tops_2(X0,sK2)
        | ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f141,plain,
    ( ~ spl6_7
    | ~ spl6_5
    | spl6_13 ),
    inference(avatar_split_clause,[],[f140,f129,f71,f79])).

fof(f79,plain,
    ( spl6_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f71,plain,
    ( spl6_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_5
    | spl6_13 ),
    inference(resolution,[],[f139,f72])).

fof(f72,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl6_13 ),
    inference(resolution,[],[f130,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f130,plain,
    ( ~ l1_pre_topc(sK2)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f134,plain,
    ( ~ spl6_13
    | spl6_14
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f125,f121,f71,f132,f129])).

fof(f121,plain,
    ( spl6_12
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_pre_topc(X2,sK0)
        | v3_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,X0),sK1)
        | ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_2(X0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(resolution,[],[f124,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f124,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK2)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_5
    | ~ spl6_12 ),
    inference(resolution,[],[f122,f72])).

fof(f122,plain,
    ( ! [X2,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | ~ r2_hidden(X1,sK1)
        | v3_pre_topc(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f123,plain,
    ( ~ spl6_7
    | spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f115,f110,f121,f79])).

fof(f110,plain,
    ( spl6_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f115,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | v3_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_10 ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
        | v3_pre_topc(X1,X2)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f111,f51])).

fof(f51,plain,(
    ! [X2,X0,X3] :
      ( ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

fof(f111,plain,
    ( ! [X0] :
        ( v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f112,plain,
    ( ~ spl6_7
    | ~ spl6_6
    | spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f106,f67,f110,f75,f79])).

fof(f67,plain,
    ( spl6_4
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f40,f68])).

fof(f68,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_tops_2(X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( spl6_9
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f87,f63,f59,f89])).

fof(f59,plain,
    ( spl6_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f63,plain,
    ( spl6_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f87,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(superposition,[],[f64,f60])).

fof(f60,plain,
    ( sK1 = sK3
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f86,plain,
    ( ~ spl6_8
    | spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f82,f59,f55,f84])).

fof(f55,plain,
    ( spl6_1
  <=> v1_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f82,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f56,f60])).

fof(f56,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f81,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ v1_tops_2(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    & v1_tops_2(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v1_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v1_tops_2(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v1_tops_2(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v1_tops_2(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
        & v1_tops_2(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v1_tops_2(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
      & v1_tops_2(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ~ v1_tops_2(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) )
   => ( ~ v1_tops_2(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f32,f75])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f73,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f33,f71])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f59])).

fof(f36,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f55])).

fof(f37,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:53:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (28390)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (28390)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (28398)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f81,f86,f91,f112,f123,f134,f141,f157,f168,f187,f190])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    ~spl6_13 | ~spl6_9 | spl6_8 | spl6_21),
% 0.21/0.49    inference(avatar_split_clause,[],[f188,f185,f84,f89,f129])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    spl6_13 <=> l1_pre_topc(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    spl6_9 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl6_8 <=> v1_tops_2(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_21 <=> r2_hidden(sK4(sK2,sK1),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f188,plain,(
% 0.21/0.49    v1_tops_2(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2) | spl6_21),
% 0.21/0.49    inference(resolution,[],[f186,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0,X1),X0) & r2_hidden(sK4(X0,X1),X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v3_pre_topc(X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(rectify,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ? [X2] : (~v3_pre_topc(X2,X0) & r2_hidden(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,X1) => v3_pre_topc(X2,X0))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tops_2)).
% 0.21/0.49  fof(f186,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK1),sK1) | spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f185])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~spl6_21 | ~spl6_6 | spl6_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f182,f164,f75,f185])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl6_6 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    spl6_18 <=> r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl6_6 | spl6_18)),
% 0.21/0.49    inference(resolution,[],[f170,f76])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f75])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK4(sK2,sK1),X0)) ) | spl6_18),
% 0.21/0.49    inference(resolution,[],[f165,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f164])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~spl6_13 | ~spl6_18 | spl6_8 | ~spl6_9 | ~spl6_17),
% 0.21/0.49    inference(avatar_split_clause,[],[f162,f155,f89,f84,f164,f129])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl6_17 <=> ! [X0] : (v1_tops_2(X0,sK2) | ~r1_tarski(sK4(sK2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(sK4(sK2,X0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v1_tops_2(sK1,sK2) | ~r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK2) | ~spl6_17),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f160])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v1_tops_2(sK1,sK2) | ~r2_hidden(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2) | ~spl6_17),
% 0.21/0.49    inference(resolution,[],[f158,f42])).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v1_tops_2(X0,sK2) | ~r2_hidden(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_17),
% 0.21/0.49    inference(resolution,[],[f156,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(rectify,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK4(sK2,X0),u1_struct_0(sK0)) | v1_tops_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~r2_hidden(sK4(sK2,X0),sK1)) ) | ~spl6_17),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~spl6_13 | spl6_17 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f153,f132,f155,f129])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl6_14 <=> ! [X0] : (~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v1_tops_2(X0,sK2) | ~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    ( ! [X0] : (v1_tops_2(X0,sK2) | ~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~r1_tarski(sK4(sK2,X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK2)) ) | ~spl6_14),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f151])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ( ! [X0] : (v1_tops_2(X0,sK2) | ~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~r1_tarski(sK4(sK2,X0),u1_struct_0(sK0)) | v1_tops_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2)) ) | ~spl6_14),
% 0.21/0.49    inference(resolution,[],[f150,f41])).
% 0.21/0.50  % (28389)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | v1_tops_2(X0,sK2) | ~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~r1_tarski(sK4(sK2,X0),u1_struct_0(sK0))) ) | ~spl6_14),
% 0.21/0.50    inference(resolution,[],[f133,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | v1_tops_2(X0,sK2) | ~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl6_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f132])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~spl6_7 | ~spl6_5 | spl6_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f140,f129,f71,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    spl6_7 <=> l1_pre_topc(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl6_5 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | (~spl6_5 | spl6_13)),
% 0.21/0.50    inference(resolution,[],[f139,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK0) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f71])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl6_13),
% 0.21/0.50    inference(resolution,[],[f130,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~l1_pre_topc(sK2) | spl6_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~spl6_13 | spl6_14 | ~spl6_5 | ~spl6_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f125,f121,f71,f132,f129])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl6_12 <=> ! [X1,X2] : (~r2_hidden(X1,sK1) | ~m1_pre_topc(X2,sK0) | v3_pre_topc(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK4(sK2,X0),sK1) | ~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK4(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_2(X0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~l1_pre_topc(sK2)) ) | (~spl6_5 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f124,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_pre_topc(sK4(X0,X1),X0) | v1_tops_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X0] : (v3_pre_topc(X0,sK2) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_5 | ~spl6_12)),
% 0.21/0.50    inference(resolution,[],[f122,f72])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~m1_pre_topc(X2,sK0) | ~r2_hidden(X1,sK1) | v3_pre_topc(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~spl6_7 | spl6_12 | ~spl6_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f115,f110,f121,f79])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    spl6_10 <=> ! [X0] : (~r2_hidden(X0,sK1) | v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~l1_pre_topc(sK0)) ) | ~spl6_10),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~r2_hidden(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X1,X2) | ~m1_pre_topc(X2,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl6_10),
% 0.21/0.50    inference(resolution,[],[f111,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X2,X0,X3] : (~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    ( ! [X0] : (v3_pre_topc(X0,sK0) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f110])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ~spl6_7 | ~spl6_6 | spl6_10 | ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f106,f67,f110,f75,f79])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    spl6_4 <=> v1_tops_2(sK1,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0)) ) | ~spl6_4),
% 0.21/0.50    inference(resolution,[],[f40,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    v1_tops_2(sK1,sK0) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f67])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~v1_tops_2(X1,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X3,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl6_9 | ~spl6_2 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f87,f63,f59,f89])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    spl6_2 <=> sK1 = sK3),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    spl6_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | (~spl6_2 | ~spl6_3)),
% 0.21/0.50    inference(superposition,[],[f64,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    sK1 = sK3 | ~spl6_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f59])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) | ~spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f63])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~spl6_8 | spl6_1 | ~spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f82,f59,f55,f84])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl6_1 <=> v1_tops_2(sK3,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~v1_tops_2(sK1,sK2) | (spl6_1 | ~spl6_2)),
% 0.21/0.50    inference(forward_demodulation,[],[f56,f60])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ~v1_tops_2(sK3,sK2) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl6_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f31,f79])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    (((~v1_tops_2(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & v1_tops_2(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f20,f19,f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & l1_pre_topc(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v1_tops_2(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) & v1_tops_2(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ? [X3] : (~v1_tops_2(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))) => (~v1_tops_2(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v1_tops_2(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v1_tops_2(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))) & v1_tops_2(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ! [X2] : (m1_pre_topc(X2,X0) => (v1_tops_2(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) => (X1 = X3 => v1_tops_2(X3,X2)))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tops_2)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl6_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f32,f75])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f71])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    m1_pre_topc(sK2,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f67])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    v1_tops_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f63])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f36,f59])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    sK1 = sK3),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f37,f55])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~v1_tops_2(sK3,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (28390)------------------------------
% 0.21/0.50  % (28390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (28390)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (28390)Memory used [KB]: 10746
% 0.21/0.50  % (28390)Time elapsed: 0.057 s
% 0.21/0.50  % (28390)------------------------------
% 0.21/0.50  % (28390)------------------------------
% 0.21/0.50  % (28383)Success in time 0.133 s
%------------------------------------------------------------------------------
