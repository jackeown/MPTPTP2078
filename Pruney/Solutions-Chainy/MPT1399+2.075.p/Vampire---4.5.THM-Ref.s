%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 216 expanded)
%              Number of leaves         :   30 (  89 expanded)
%              Depth                    :   11
%              Number of atoms          :  439 (1364 expanded)
%              Number of equality atoms :   22 ( 100 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f65,f70,f75,f80,f88,f96,f104,f109,f122,f127,f155,f173,f197,f202,f209,f218,f221])).

fof(f221,plain,(
    ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f219,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f219,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_21 ),
    inference(resolution,[],[f181,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f181,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl3_21
  <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f218,plain,
    ( ~ spl3_11
    | spl3_12
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_11
    | spl3_12
    | spl3_24 ),
    inference(subsumption_resolution,[],[f216,f121])).

% (23124)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f121,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_11
  <=> m1_subset_1(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f216,plain,
    ( ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_12
    | spl3_24 ),
    inference(subsumption_resolution,[],[f213,f126])).

fof(f126,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f213,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k2_struct_0(sK0))
    | spl3_24 ),
    inference(resolution,[],[f196,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f196,plain,
    ( ~ r2_hidden(sK1,k2_struct_0(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl3_24
  <=> r2_hidden(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f209,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_23 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_23 ),
    inference(subsumption_resolution,[],[f207,f74])).

fof(f74,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f207,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_4
    | spl3_23 ),
    inference(subsumption_resolution,[],[f205,f69])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_23 ),
    inference(resolution,[],[f192,f44])).

fof(f44,plain,(
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

fof(f192,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl3_23
  <=> v4_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f202,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | spl3_22 ),
    inference(subsumption_resolution,[],[f200,f74])).

fof(f200,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl3_4
    | spl3_22 ),
    inference(subsumption_resolution,[],[f198,f69])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl3_22 ),
    inference(resolution,[],[f188,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f188,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_22
  <=> v3_pre_topc(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f197,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | spl3_21
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f184,f171,f152,f180,f194,f190,f186])).

fof(f152,plain,
    ( spl3_16
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f171,plain,
    ( spl3_19
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f184,plain,
    ( r2_hidden(k2_struct_0(sK0),k1_xboole_0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0))
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f172,f154])).

fof(f154,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f172,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f173,plain,
    ( spl3_19
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f169,f106,f52,f171])).

fof(f52,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f169,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
        | r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0) )
    | ~ spl3_1
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f168,f108])).

fof(f108,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f168,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(sK1,X3)
        | ~ v4_pre_topc(X3,sK0)
        | ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f40,f54])).

fof(f54,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f52])).

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

% (23125)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% (23106)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f155,plain,
    ( spl3_16
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f150,f106,f101,f152])).

fof(f101,plain,
    ( spl3_9
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f150,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f103,f108])).

fof(f103,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f127,plain,
    ( ~ spl3_12
    | spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f115,f106,f93,f124])).

fof(f93,plain,
    ( spl3_8
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f115,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl3_8
    | ~ spl3_10 ),
    inference(superposition,[],[f95,f108])).

fof(f95,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f122,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f114,f106,f62,f119])).

fof(f62,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f114,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f64,f108])).

fof(f64,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f109,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f85,f106])).

fof(f85,plain,
    ( spl3_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f99,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f87,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f87,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f98,f85,f101])).

fof(f98,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(resolution,[],[f87,f46])).

fof(f46,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f96,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f91,f77,f93,f85])).

fof(f77,plain,
    ( spl3_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f91,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | spl3_6 ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f79,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

% (23107)Refutation not found, incomplete strategy% (23107)------------------------------
% (23107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23107)Termination reason: Refutation not found, incomplete strategy

% (23107)Memory used [KB]: 10618
% (23107)Time elapsed: 0.107 s
% (23107)------------------------------
% (23107)------------------------------
fof(f88,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f81,f67,f85])).

fof(f81,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f80,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f33,f72])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f55,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f41,f52])).

fof(f41,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:44:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (23119)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (23108)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (23104)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (23109)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.52  % (23107)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.52  % (23127)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (23116)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (23111)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (23105)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (23127)Refutation not found, incomplete strategy% (23127)------------------------------
% 0.21/0.52  % (23127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23127)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23127)Memory used [KB]: 10618
% 0.21/0.53  % (23127)Time elapsed: 0.063 s
% 0.21/0.53  % (23127)------------------------------
% 0.21/0.53  % (23127)------------------------------
% 0.21/0.53  % (23111)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f222,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f55,f65,f70,f75,f80,f88,f96,f104,f109,f122,f127,f155,f173,f197,f202,f209,f218,f221])).
% 0.21/0.53  fof(f221,plain,(
% 0.21/0.53    ~spl3_21),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.53  fof(f220,plain,(
% 0.21/0.53    $false | ~spl3_21),
% 0.21/0.53    inference(subsumption_resolution,[],[f219,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_21),
% 0.21/0.53    inference(resolution,[],[f181,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~spl3_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f180])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl3_21 <=> r2_hidden(k2_struct_0(sK0),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    ~spl3_11 | spl3_12 | spl3_24),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f217])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    $false | (~spl3_11 | spl3_12 | spl3_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f216,f121])).
% 0.21/0.53  % (23124)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    m1_subset_1(sK1,k2_struct_0(sK0)) | ~spl3_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f119])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl3_11 <=> m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,k2_struct_0(sK0)) | (spl3_12 | spl3_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f213,f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | spl3_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl3_12 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k2_struct_0(sK0)) | spl3_24),
% 0.21/0.53    inference(resolution,[],[f196,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.53  fof(f196,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k2_struct_0(sK0)) | spl3_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    spl3_24 <=> r2_hidden(sK1,k2_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ~spl3_4 | ~spl3_5 | spl3_23),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f208])).
% 0.21/0.53  fof(f208,plain,(
% 0.21/0.53    $false | (~spl3_4 | ~spl3_5 | spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f207,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl3_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl3_5 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.53  fof(f207,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | (~spl3_4 | spl3_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f205,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl3_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    spl3_4 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.53  fof(f205,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_23),
% 0.21/0.53    inference(resolution,[],[f192,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~v4_pre_topc(k2_struct_0(sK0),sK0) | spl3_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    spl3_23 <=> v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ~spl3_4 | ~spl3_5 | spl3_22),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f201])).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    $false | (~spl3_4 | ~spl3_5 | spl3_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f200,f74])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    ~v2_pre_topc(sK0) | (~spl3_4 | spl3_22)),
% 0.21/0.53    inference(subsumption_resolution,[],[f198,f69])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl3_22),
% 0.21/0.53    inference(resolution,[],[f188,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ~v3_pre_topc(k2_struct_0(sK0),sK0) | spl3_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f186])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl3_22 <=> v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    ~spl3_22 | ~spl3_23 | ~spl3_24 | spl3_21 | ~spl3_16 | ~spl3_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f184,f171,f152,f180,f194,f190,f186])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    spl3_16 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl3_19 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    r2_hidden(k2_struct_0(sK0),k1_xboole_0) | ~r2_hidden(sK1,k2_struct_0(sK0)) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~v3_pre_topc(k2_struct_0(sK0),sK0) | (~spl3_16 | ~spl3_19)),
% 0.21/0.53    inference(resolution,[],[f172,f154])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f152])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | ~spl3_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    spl3_19 | ~spl3_1 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f169,f106,f52,f171])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    spl3_1 <=> k1_xboole_0 = sK2),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) ) | (~spl3_1 | ~spl3_10)),
% 0.21/0.53    inference(forward_demodulation,[],[f168,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f106])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_1),
% 0.21/0.53    inference(forward_demodulation,[],[f40,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    k1_xboole_0 = sK2 | ~spl3_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f52])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ((k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f30,f29,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  % (23125)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.53  % (23106)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) => (k1_xboole_0 = sK2 & ! [X3] : (((r2_hidden(X3,sK2) | ~r2_hidden(sK1,X3) | ~v4_pre_topc(X3,sK0) | ~v3_pre_topc(X3,sK0)) & ((r2_hidden(sK1,X3) & v4_pre_topc(X3,sK0) & v3_pre_topc(X3,sK0)) | ~r2_hidden(X3,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.21/0.53  fof(f155,plain,(
% 0.21/0.53    spl3_16 | ~spl3_9 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f150,f106,f101,f152])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    spl3_9 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_9 | ~spl3_10)),
% 0.21/0.53    inference(forward_demodulation,[],[f103,f108])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f101])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    ~spl3_12 | spl3_8 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f115,f106,f93,f124])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    spl3_8 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~v1_xboole_0(k2_struct_0(sK0)) | (spl3_8 | ~spl3_10)),
% 0.21/0.53    inference(superposition,[],[f95,f108])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f93])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    spl3_11 | ~spl3_3 | ~spl3_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f114,f106,f62,f119])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    m1_subset_1(sK1,k2_struct_0(sK0)) | (~spl3_3 | ~spl3_10)),
% 0.21/0.53    inference(superposition,[],[f64,f108])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f62])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl3_10 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f99,f85,f106])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    spl3_7 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_7),
% 0.21/0.53    inference(resolution,[],[f87,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl3_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f85])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl3_9 | ~spl3_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f98,f85,f101])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.21/0.53    inference(resolution,[],[f87,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~spl3_7 | ~spl3_8 | spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f91,f77,f93,f85])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    spl3_6 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0) | spl3_6),
% 0.21/0.53    inference(resolution,[],[f79,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ~v2_struct_0(sK0) | spl3_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f77])).
% 0.21/0.53  % (23107)Refutation not found, incomplete strategy% (23107)------------------------------
% 0.21/0.53  % (23107)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23107)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23107)Memory used [KB]: 10618
% 0.21/0.53  % (23107)Time elapsed: 0.107 s
% 0.21/0.53  % (23107)------------------------------
% 0.21/0.53  % (23107)------------------------------
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl3_7 | ~spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f81,f67,f85])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl3_4),
% 0.21/0.53    inference(resolution,[],[f69,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ~spl3_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f77])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    spl3_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f72])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl3_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f67])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl3_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    spl3_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f41,f52])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    k1_xboole_0 = sK2),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (23111)------------------------------
% 0.21/0.53  % (23111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23111)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (23111)Memory used [KB]: 6268
% 0.21/0.53  % (23111)Time elapsed: 0.061 s
% 0.21/0.53  % (23111)------------------------------
% 0.21/0.53  % (23111)------------------------------
% 0.21/0.53  % (23110)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (23120)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.53  % (23103)Success in time 0.171 s
%------------------------------------------------------------------------------
