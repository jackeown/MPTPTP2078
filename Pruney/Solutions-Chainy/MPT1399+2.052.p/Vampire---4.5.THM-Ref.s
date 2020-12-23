%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 357 expanded)
%              Number of leaves         :   33 ( 134 expanded)
%              Depth                    :   16
%              Number of atoms          :  524 (2852 expanded)
%              Number of equality atoms :   43 ( 243 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f305,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f124,f140,f161,f194,f211,f265,f303])).

fof(f303,plain,
    ( ~ spl5_4
    | spl5_8
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl5_4
    | spl5_8
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f296,f111])).

fof(f111,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f296,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_4
    | spl5_8
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f160,f293])).

fof(f293,plain,
    ( sK2 = sK3(sK0)
    | ~ spl5_4
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f268,f91])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f76,f59])).

fof(f59,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k1_xboole_0 = sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK2)
            | ~ r2_hidden(sK1,X3)
            | ~ v4_pre_topc(X3,sK0)
            | ~ v3_pre_topc(X3,sK0) )
          & ( ( r2_hidden(sK1,X3)
              & v4_pre_topc(X3,sK0)
              & v3_pre_topc(X3,sK0) )
            | ~ r2_hidden(X3,sK2) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK0)
                      | ~ v3_pre_topc(X3,sK0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK0)
                        & v3_pre_topc(X3,sK0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X1,X3)
                    | ~ v4_pre_topc(X3,sK0)
                    | ~ v3_pre_topc(X3,sK0) )
                  & ( ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,sK0)
                      & v3_pre_topc(X3,sK0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(sK1,X3)
                  | ~ v4_pre_topc(X3,sK0)
                  | ~ v3_pre_topc(X3,sK0) )
                & ( ( r2_hidden(sK1,X3)
                    & v4_pre_topc(X3,sK0)
                    & v3_pre_topc(X3,sK0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k1_xboole_0 = X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,X2)
                | ~ r2_hidden(sK1,X3)
                | ~ v4_pre_topc(X3,sK0)
                | ~ v3_pre_topc(X3,sK0) )
              & ( ( r2_hidden(sK1,X3)
                  & v4_pre_topc(X3,sK0)
                  & v3_pre_topc(X3,sK0) )
                | ~ r2_hidden(X3,X2) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
   => ( k1_xboole_0 = sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK2)
              | ~ r2_hidden(sK1,X3)
              | ~ v4_pre_topc(X3,sK0)
              | ~ v3_pre_topc(X3,sK0) )
            & ( ( r2_hidden(sK1,X3)
                & v4_pre_topc(X3,sK0)
                & v3_pre_topc(X3,sK0) )
              | ~ r2_hidden(X3,sK2) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK4(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f48])).

% (32708)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK4(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f268,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(sK0))
    | ~ spl5_4
    | ~ spl5_19 ),
    inference(unit_resulting_resolution,[],[f111,f264,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f264,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl5_19
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f160,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl5_8
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f265,plain,
    ( spl5_19
    | ~ spl5_7
    | spl5_11
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f241,f208,f191,f137,f262])).

fof(f137,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f191,plain,
    ( spl5_11
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f208,plain,
    ( spl5_14
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f241,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))
    | ~ spl5_7
    | spl5_11
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f210,f229])).

fof(f229,plain,
    ( sK2 = k2_struct_0(sK0)
    | ~ spl5_7
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f193,f139,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1)
      | sK2 = X1 ) ),
    inference(forward_demodulation,[],[f172,f86])).

fof(f86,plain,(
    ! [X0] : k3_subset_1(X0,sK2) = X0 ),
    inference(definition_unfolding,[],[f63,f83])).

fof(f83,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,sK2) ),
    inference(definition_unfolding,[],[f66,f82])).

fof(f82,plain,(
    ! [X0] : k1_subset_1(X0) = sK2 ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k3_subset_1(X1,sK2))
      | sK2 = X1 ) ),
    inference(subsumption_resolution,[],[f170,f125])).

fof(f125,plain,(
    ! [X0] : ~ r2_hidden(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f85,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f85,plain,(
    ! [X0] : r1_tarski(sK2,X0) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,k3_subset_1(X1,sK2))
      | sK2 = X1 ) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK2,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f64,f59])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | r2_hidden(X2,k3_subset_1(X0,X1))
      | sK2 = X0 ) ),
    inference(definition_unfolding,[],[f69,f59])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k3_subset_1(X0,X1))
      | r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k3_subset_1(X0,X1))
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ( ~ r2_hidden(X2,X1)
               => r2_hidden(X2,k3_subset_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).

fof(f139,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f137])).

fof(f193,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f210,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f208])).

fof(f211,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f178,f121,f104,f99,f94,f208])).

fof(f94,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f99,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f104,plain,
    ( spl5_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f121,plain,
    ( spl5_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f178,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f174,f131])).

fof(f131,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f123,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f123,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f174,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f70])).

% (32698)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK3(X0),X0)
        & v3_pre_topc(sK3(X0),X0)
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f106,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f101,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f96,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f194,plain,
    ( ~ spl5_11
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f150,f121,f104,f99,f191])).

fof(f150,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f149,f129])).

fof(f129,plain,
    ( v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f101,f106,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f149,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f148,f127])).

fof(f127,plain,
    ( v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f101,f106,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f148,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f135,f92])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f88,f86])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f65,f83])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f135,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f134,f125])).

fof(f134,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,sK2)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f58,f131])).

fof(f58,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f161,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f141,f104,f99,f94,f158])).

fof(f141,plain,
    ( ~ v1_xboole_0(sK3(sK0))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f140,plain,
    ( spl5_7
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f133,f121,f114,f137])).

fof(f114,plain,
    ( spl5_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f133,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl5_5
    | ~ spl5_6 ),
    inference(backward_demodulation,[],[f116,f131])).

fof(f116,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f124,plain,
    ( spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f118,f104,f121])).

fof(f118,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f106,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

% (32710)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
fof(f117,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f53,f114])).

fof(f53,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f112,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f84,f109])).

fof(f84,plain,(
    v1_xboole_0(sK2) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f97,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:49:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.20/0.43  % (32705)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.44  % (32705)Refutation not found, incomplete strategy% (32705)------------------------------
% 0.20/0.44  % (32705)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (32705)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.44  
% 0.20/0.44  % (32705)Memory used [KB]: 10746
% 0.20/0.44  % (32705)Time elapsed: 0.007 s
% 0.20/0.44  % (32705)------------------------------
% 0.20/0.44  % (32705)------------------------------
% 0.20/0.45  % (32709)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.45  % (32707)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (32696)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (32709)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f305,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f124,f140,f161,f194,f211,f265,f303])).
% 0.20/0.46  fof(f303,plain,(
% 0.20/0.46    ~spl5_4 | spl5_8 | ~spl5_19),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f302])).
% 0.20/0.46  fof(f302,plain,(
% 0.20/0.46    $false | (~spl5_4 | spl5_8 | ~spl5_19)),
% 0.20/0.46    inference(subsumption_resolution,[],[f296,f111])).
% 0.20/0.46  fof(f111,plain,(
% 0.20/0.46    v1_xboole_0(sK2) | ~spl5_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f109])).
% 0.20/0.46  fof(f109,plain,(
% 0.20/0.46    spl5_4 <=> v1_xboole_0(sK2)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.46  fof(f296,plain,(
% 0.20/0.46    ~v1_xboole_0(sK2) | (~spl5_4 | spl5_8 | ~spl5_19)),
% 0.20/0.46    inference(backward_demodulation,[],[f160,f293])).
% 0.20/0.46  fof(f293,plain,(
% 0.20/0.46    sK2 = sK3(sK0) | (~spl5_4 | ~spl5_19)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f268,f91])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | sK2 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f76,f59])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    k1_xboole_0 = sK2),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f44,f43,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(nnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f21])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f20])).
% 0.20/0.46  fof(f20,negated_conjecture,(
% 0.20/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.46    inference(negated_conjecture,[],[f19])).
% 0.20/0.46  fof(f19,conjecture,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f49])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK4(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f34,f48])).
% 0.20/0.46  % (32708)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK4(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK4(X0),X0)))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(flattening,[],[f33])).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,axiom,(
% 0.20/0.46    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.46  fof(f268,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK3(sK0))) ) | (~spl5_4 | ~spl5_19)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f111,f264,f81])).
% 0.20/0.46  fof(f81,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.46  fof(f264,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | ~spl5_19),
% 0.20/0.46    inference(avatar_component_clause,[],[f262])).
% 0.20/0.46  fof(f262,plain,(
% 0.20/0.46    spl5_19 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.46  fof(f160,plain,(
% 0.20/0.46    ~v1_xboole_0(sK3(sK0)) | spl5_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f158])).
% 0.20/0.46  fof(f158,plain,(
% 0.20/0.46    spl5_8 <=> v1_xboole_0(sK3(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.46  fof(f265,plain,(
% 0.20/0.46    spl5_19 | ~spl5_7 | spl5_11 | ~spl5_14),
% 0.20/0.46    inference(avatar_split_clause,[],[f241,f208,f191,f137,f262])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    spl5_7 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    spl5_11 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.46  fof(f208,plain,(
% 0.20/0.46    spl5_14 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.46  fof(f241,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0),k1_zfmisc_1(sK2)) | (~spl5_7 | spl5_11 | ~spl5_14)),
% 0.20/0.46    inference(backward_demodulation,[],[f210,f229])).
% 0.20/0.46  fof(f229,plain,(
% 0.20/0.46    sK2 = k2_struct_0(sK0) | (~spl5_7 | spl5_11)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f193,f139,f173])).
% 0.20/0.46  fof(f173,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~m1_subset_1(X0,X1) | sK2 = X1) )),
% 0.20/0.46    inference(forward_demodulation,[],[f172,f86])).
% 0.20/0.46  fof(f86,plain,(
% 0.20/0.46    ( ! [X0] : (k3_subset_1(X0,sK2) = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f63,f83])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,sK2)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f66,f82])).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ( ! [X0] : (k1_subset_1(X0) = sK2) )),
% 0.20/0.46    inference(definition_unfolding,[],[f62,f59])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.46  fof(f172,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | r2_hidden(X0,k3_subset_1(X1,sK2)) | sK2 = X1) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f170,f125])).
% 0.20/0.46  fof(f125,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK2)) )),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f85,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.46  fof(f85,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(sK2,X0)) )),
% 0.20/0.46    inference(definition_unfolding,[],[f61,f59])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.46  fof(f170,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r2_hidden(X0,sK2) | ~m1_subset_1(X0,X1) | r2_hidden(X0,k3_subset_1(X1,sK2)) | sK2 = X1) )),
% 0.20/0.46    inference(resolution,[],[f89,f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f64,f59])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.46  fof(f89,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | r2_hidden(X2,k3_subset_1(X0,X1)) | sK2 = X0) )),
% 0.20/0.46    inference(definition_unfolding,[],[f69,f59])).
% 0.20/0.46  fof(f69,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(flattening,[],[f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k3_subset_1(X0,X1)) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,axiom,(
% 0.20/0.46    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,X0) => (~r2_hidden(X2,X1) => r2_hidden(X2,k3_subset_1(X0,X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_subset_1)).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl5_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f137])).
% 0.20/0.46  fof(f193,plain,(
% 0.20/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl5_11),
% 0.20/0.46    inference(avatar_component_clause,[],[f191])).
% 0.20/0.46  fof(f210,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_14),
% 0.20/0.46    inference(avatar_component_clause,[],[f208])).
% 0.20/0.46  fof(f211,plain,(
% 0.20/0.46    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f178,f121,f104,f99,f94,f208])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    spl5_1 <=> v2_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    spl5_2 <=> v2_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.46  fof(f104,plain,(
% 0.20/0.46    spl5_3 <=> l1_pre_topc(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    spl5_6 <=> l1_struct_0(sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.46  fof(f178,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.20/0.46    inference(forward_demodulation,[],[f174,f131])).
% 0.20/0.46  fof(f131,plain,(
% 0.20/0.46    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_6),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f123,f67])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,axiom,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    l1_struct_0(sK0) | ~spl5_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f121])).
% 0.20/0.46  fof(f174,plain,(
% 0.20/0.46    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f96,f101,f106,f70])).
% 0.20/0.46  % (32698)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ! [X0] : ((v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK3(X0),X0) & v3_pre_topc(sK3(X0),X0) & ~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    l1_pre_topc(sK0) | ~spl5_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f104])).
% 0.20/0.46  fof(f101,plain,(
% 0.20/0.46    v2_pre_topc(sK0) | ~spl5_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f99])).
% 0.20/0.46  fof(f96,plain,(
% 0.20/0.46    ~v2_struct_0(sK0) | spl5_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f94])).
% 0.20/0.46  fof(f194,plain,(
% 0.20/0.46    ~spl5_11 | ~spl5_2 | ~spl5_3 | ~spl5_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f150,f121,f104,f99,f191])).
% 0.20/0.46  fof(f150,plain,(
% 0.20/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.20/0.46    inference(subsumption_resolution,[],[f149,f129])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl5_2 | ~spl5_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f101,f106,f75])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.46  fof(f149,plain,(
% 0.20/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl5_2 | ~spl5_3 | ~spl5_6)),
% 0.20/0.46    inference(subsumption_resolution,[],[f148,f127])).
% 0.20/0.46  fof(f127,plain,(
% 0.20/0.46    v4_pre_topc(k2_struct_0(sK0),sK0) | (~spl5_2 | ~spl5_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f101,f106,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,axiom,(
% 0.20/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~spl5_6),
% 0.20/0.46    inference(resolution,[],[f135,f92])).
% 0.20/0.46  fof(f92,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(forward_demodulation,[],[f88,f86])).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,sK2),k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f65,f83])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | ~spl5_6),
% 0.20/0.46    inference(subsumption_resolution,[],[f134,f125])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | ~spl5_6),
% 0.20/0.46    inference(backward_demodulation,[],[f58,f131])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  fof(f161,plain,(
% 0.20/0.46    ~spl5_8 | spl5_1 | ~spl5_2 | ~spl5_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f141,f104,f99,f94,f158])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    ~v1_xboole_0(sK3(sK0)) | (spl5_1 | ~spl5_2 | ~spl5_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f96,f101,f106,f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f47])).
% 0.20/0.46  fof(f140,plain,(
% 0.20/0.46    spl5_7 | ~spl5_5 | ~spl5_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f133,f121,f114,f137])).
% 0.20/0.46  fof(f114,plain,(
% 0.20/0.46    spl5_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl5_5 | ~spl5_6)),
% 0.20/0.46    inference(backward_demodulation,[],[f116,f131])).
% 0.20/0.46  fof(f116,plain,(
% 0.20/0.46    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f114])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    spl5_6 | ~spl5_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f118,f104,f121])).
% 0.20/0.46  fof(f118,plain,(
% 0.20/0.46    l1_struct_0(sK0) | ~spl5_3),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f106,f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.46  % (32710)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.46  fof(f117,plain,(
% 0.20/0.46    spl5_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f53,f114])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  fof(f112,plain,(
% 0.20/0.46    spl5_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f84,f109])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    v1_xboole_0(sK2)),
% 0.20/0.46    inference(definition_unfolding,[],[f60,f59])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    v1_xboole_0(k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    spl5_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f52,f104])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  fof(f102,plain,(
% 0.20/0.46    spl5_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f51,f99])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    v2_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  fof(f97,plain,(
% 0.20/0.46    ~spl5_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f50,f94])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ~v2_struct_0(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f45])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (32709)------------------------------
% 0.20/0.46  % (32709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (32709)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (32709)Memory used [KB]: 10746
% 0.20/0.46  % (32709)Time elapsed: 0.051 s
% 0.20/0.46  % (32709)------------------------------
% 0.20/0.46  % (32709)------------------------------
% 0.20/0.47  % (32687)Success in time 0.123 s
%------------------------------------------------------------------------------
