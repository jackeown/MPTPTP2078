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
% DateTime   : Thu Dec  3 13:15:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 200 expanded)
%              Number of leaves         :   28 (  78 expanded)
%              Depth                    :   11
%              Number of atoms          :  427 (1328 expanded)
%              Number of equality atoms :   24 ( 102 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f66,f71,f76,f81,f89,f97,f104,f113,f151,f173,f183,f194,f200,f204])).

fof(f204,plain,(
    ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f202,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f202,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_17 ),
    inference(resolution,[],[f160,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f160,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl3_17
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f200,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_20 ),
    inference(subsumption_resolution,[],[f198,f75])).

fof(f75,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f198,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_4
    | spl3_20 ),
    inference(subsumption_resolution,[],[f196,f70])).

fof(f70,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f196,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_20 ),
    inference(resolution,[],[f172,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f172,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_20
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f194,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_19 ),
    inference(subsumption_resolution,[],[f192,f75])).

fof(f192,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f190,f70])).

fof(f190,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_19 ),
    inference(resolution,[],[f168,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f168,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl3_19
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f183,plain,
    ( spl3_8
    | ~ spl3_10
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | spl3_8
    | ~ spl3_10
    | spl3_18 ),
    inference(subsumption_resolution,[],[f181,f112])).

fof(f112,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_10
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f181,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_8
    | spl3_18 ),
    inference(subsumption_resolution,[],[f175,f96])).

fof(f96,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_8
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f175,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_18 ),
    inference(resolution,[],[f164,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f164,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl3_18
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f173,plain,
    ( spl3_17
    | ~ spl3_18
    | ~ spl3_19
    | ~ spl3_20
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f156,f149,f170,f166,f162,f158])).

fof(f149,plain,
    ( spl3_16
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f156,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f155,f49])).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f155,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f154,f49])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f153,f49])).

fof(f153,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_subset_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f152,f49])).

fof(f152,plain,
    ( r2_hidden(k2_subset_1(k2_struct_0(sK0)),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_subset_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f150,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f150,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f147,f101,f53,f149])).

fof(f53,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f101,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f147,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f146,f103])).

fof(f103,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f146,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f40,f55])).

fof(f55,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f40,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK2)
      | ~ r2_hidden(sK1,X3)
      | ~ v4_pre_topc(X3,sK0)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
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

fof(f30,plain,
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f113,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f108,f101,f63,f110])).

fof(f63,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f108,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f65,f103])).

fof(f65,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f86,f101])).

fof(f86,plain,
    ( spl3_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f88,f46])).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f88,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f97,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f92,f78,f94,f86])).

fof(f78,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f92,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl3_6 ),
    inference(resolution,[],[f80,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f80,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f89,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f82,f68,f86])).

fof(f82,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f81,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f41,f53])).

fof(f41,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (32683)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.45  % (32675)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.45  % (32683)Refutation not found, incomplete strategy% (32683)------------------------------
% 0.21/0.45  % (32683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (32683)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (32683)Memory used [KB]: 10618
% 0.21/0.45  % (32683)Time elapsed: 0.035 s
% 0.21/0.45  % (32683)------------------------------
% 0.21/0.45  % (32683)------------------------------
% 0.21/0.46  % (32667)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (32667)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f205,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f56,f66,f71,f76,f81,f89,f97,f104,f113,f151,f173,f183,f194,f200,f204])).
% 0.21/0.46  fof(f204,plain,(
% 0.21/0.46    ~spl3_17),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f203])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    $false | ~spl3_17),
% 0.21/0.46    inference(subsumption_resolution,[],[f202,f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_17),
% 0.21/0.46    inference(resolution,[],[f160,f48])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,axiom,(
% 0.21/0.46    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.46  fof(f160,plain,(
% 0.21/0.46    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f158])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    spl3_17 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.46  fof(f200,plain,(
% 0.21/0.46    ~spl3_4 | ~spl3_5 | spl3_20),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f199])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    $false | (~spl3_4 | ~spl3_5 | spl3_20)),
% 0.21/0.46    inference(subsumption_resolution,[],[f198,f75])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    v2_pre_topc(sK0) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_5 <=> v2_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f198,plain,(
% 0.21/0.46    ~v2_pre_topc(sK0) | (~spl3_4 | spl3_20)),
% 0.21/0.46    inference(subsumption_resolution,[],[f196,f70])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f68])).
% 0.21/0.46  fof(f68,plain,(
% 0.21/0.46    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.46  fof(f196,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_20),
% 0.21/0.46    inference(resolution,[],[f172,f44])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl3_20),
% 0.21/0.46    inference(avatar_component_clause,[],[f170])).
% 0.21/0.46  fof(f170,plain,(
% 0.21/0.46    spl3_20 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    ~spl3_4 | ~spl3_5 | spl3_19),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f193])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    $false | (~spl3_4 | ~spl3_5 | spl3_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f192,f75])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    ~v2_pre_topc(sK0) | (~spl3_4 | spl3_19)),
% 0.21/0.46    inference(subsumption_resolution,[],[f190,f70])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_19),
% 0.21/0.46    inference(resolution,[],[f168,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.46  fof(f168,plain,(
% 0.21/0.46    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f166])).
% 0.21/0.46  fof(f166,plain,(
% 0.21/0.46    spl3_19 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    spl3_8 | ~spl3_10 | spl3_18),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f182])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    $false | (spl3_8 | ~spl3_10 | spl3_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f181,f112])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl3_10 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ~m1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_8 | spl3_18)),
% 0.21/0.46    inference(subsumption_resolution,[],[f175,f96])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl3_8 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f175,plain,(
% 0.21/0.46    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl3_18),
% 0.21/0.46    inference(resolution,[],[f164,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.46  fof(f164,plain,(
% 0.21/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f162])).
% 0.21/0.46  fof(f162,plain,(
% 0.21/0.46    spl3_18 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f173,plain,(
% 0.21/0.46    spl3_17 | ~spl3_18 | ~spl3_19 | ~spl3_20 | ~spl3_16),
% 0.21/0.46    inference(avatar_split_clause,[],[f156,f149,f170,f166,f162,f158])).
% 0.21/0.46  fof(f149,plain,(
% 0.21/0.46    spl3_16 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f156,plain,(
% 0.21/0.46    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_16),
% 0.21/0.46    inference(forward_demodulation,[],[f155,f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.46  fof(f155,plain,(
% 0.21/0.46    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~spl3_16),
% 0.21/0.46    inference(forward_demodulation,[],[f154,f49])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ~r2_hidden(sK1,k2_struct_0(sK0)) | r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~spl3_16),
% 0.21/0.46    inference(forward_demodulation,[],[f153,f49])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,k2_subset_1(k2_struct_0(sK0))) | ~v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~spl3_16),
% 0.21/0.46    inference(forward_demodulation,[],[f152,f49])).
% 0.21/0.46  fof(f152,plain,(
% 0.21/0.46    r2_hidden(k2_subset_1(k2_struct_0(sK0)),k1_xboole_0) | ~r2_hidden(sK1,k2_subset_1(k2_struct_0(sK0))) | ~v4_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~v3_pre_topc(k2_subset_1(k2_struct_0(sK0)),sK0) | ~spl3_16),
% 0.21/0.46    inference(resolution,[],[f150,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.46  fof(f150,plain,(
% 0.21/0.46    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f149])).
% 0.21/0.46  fof(f151,plain,(
% 0.21/0.46    spl3_16 | ~spl3_1 | ~spl3_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f147,f101,f53,f149])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    spl3_1 <=> k1_xboole_0 = sK2),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f147,plain,(
% 0.21/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | (~spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(forward_demodulation,[],[f146,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 0.21/0.47    inference(forward_demodulation,[],[f40,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    k1_xboole_0 = sK2 | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(nnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f11])).
% 0.21/0.47  fof(f11,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl3_10 | ~spl3_3 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f108,f101,f63,f110])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_9)),
% 0.21/0.47    inference(superposition,[],[f65,f103])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl3_9 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f99,f86,f101])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl3_7 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_7),
% 0.21/0.47    inference(resolution,[],[f88,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~spl3_7 | ~spl3_8 | spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f92,f78,f94,f86])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_6 <=> v2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | spl3_6),
% 0.21/0.47    inference(resolution,[],[f80,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~v2_struct_0(sK0) | spl3_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    spl3_7 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f82,f68,f86])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f70,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f73])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f68])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f63])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f53])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    k1_xboole_0 = sK2),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (32667)------------------------------
% 0.21/0.47  % (32667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (32667)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (32667)Memory used [KB]: 6268
% 0.21/0.47  % (32667)Time elapsed: 0.051 s
% 0.21/0.47  % (32667)------------------------------
% 0.21/0.47  % (32667)------------------------------
% 0.21/0.47  % (32659)Success in time 0.112 s
%------------------------------------------------------------------------------
