%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 179 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :  282 ( 796 expanded)
%              Number of equality atoms :   18 (  59 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1306)Termination reason: Refutation not found, incomplete strategy
fof(f479,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f86,f97,f101,f234,f256,f420,f439,f445,f478])).

% (1306)Memory used [KB]: 6396
% (1306)Time elapsed: 0.098 s
% (1306)------------------------------
% (1306)------------------------------
fof(f478,plain,
    ( ~ spl5_26
    | spl5_27 ),
    inference(avatar_split_clause,[],[f474,f253,f249])).

fof(f249,plain,
    ( spl5_26
  <=> r2_hidden(sK3(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f253,plain,
    ( spl5_27
  <=> r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f474,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_27 ),
    inference(resolution,[],[f255,f131])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f73,plain,(
    r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f25,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f255,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f253])).

fof(f445,plain,
    ( spl5_1
    | spl5_23 ),
    inference(avatar_split_clause,[],[f402,f227,f50])).

fof(f50,plain,
    ( spl5_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f227,plain,
    ( spl5_23
  <=> r2_hidden(sK3(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f402,plain,
    ( r1_tarski(sK1,sK2)
    | spl5_23 ),
    inference(resolution,[],[f229,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f229,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f227])).

fof(f439,plain,
    ( ~ spl5_23
    | spl5_24 ),
    inference(avatar_split_clause,[],[f436,f231,f227])).

fof(f231,plain,
    ( spl5_24
  <=> r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f436,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_24 ),
    inference(resolution,[],[f233,f103])).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f61,f37])).

fof(f61,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f40])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f233,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | spl5_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f420,plain,
    ( spl5_2
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f414])).

fof(f414,plain,
    ( $false
    | spl5_2
    | spl5_26 ),
    inference(resolution,[],[f251,f88])).

fof(f88,plain,
    ( r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_2 ),
    inference(resolution,[],[f56,f38])).

fof(f56,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl5_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f251,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_26 ),
    inference(avatar_component_clause,[],[f249])).

fof(f256,plain,
    ( ~ spl5_26
    | ~ spl5_27
    | spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f244,f99,f54,f253,f249])).

fof(f99,plain,
    ( spl5_7
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f244,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK2,sK1),sK2)
    | spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f89,f100])).

fof(f100,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f89,plain,
    ( ~ r2_hidden(sK3(sK2,sK1),sK1)
    | spl5_2 ),
    inference(resolution,[],[f56,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f234,plain,
    ( ~ spl5_23
    | ~ spl5_24
    | spl5_1
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f222,f84,f50,f231,f227])).

fof(f84,plain,
    ( spl5_6
  <=> ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
        | r2_hidden(X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f222,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK3(sK1,sK2),sK1)
    | spl5_1
    | ~ spl5_6 ),
    inference(resolution,[],[f60,f85])).

fof(f85,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f60,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK2)
    | spl5_1 ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f101,plain,
    ( spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f91,f99,f80])).

fof(f80,plain,
    ( spl5_5
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f27,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f27,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f97,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl5_5 ),
    inference(resolution,[],[f82,f29])).

fof(f29,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f82,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f86,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f77,f84,f80])).

fof(f77,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0))
      | v1_xboole_0(k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f26,f31])).

fof(f26,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f48,f54,f50])).

fof(f48,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f45,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X0,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(equality_proxy_replacement,[],[f36,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f45,plain,(
    ~ sQ4_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f28,f44])).

fof(f28,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:40:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1306)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (1317)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (1309)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (1320)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (1303)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (1306)Refutation not found, incomplete strategy% (1306)------------------------------
% 0.22/0.52  % (1306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (1317)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (1310)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (1306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  fof(f479,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f57,f86,f97,f101,f234,f256,f420,f439,f445,f478])).
% 0.22/0.53  
% 0.22/0.53  % (1306)Memory used [KB]: 6396
% 0.22/0.53  % (1306)Time elapsed: 0.098 s
% 0.22/0.53  % (1306)------------------------------
% 0.22/0.53  % (1306)------------------------------
% 0.22/0.54  fof(f478,plain,(
% 0.22/0.54    ~spl5_26 | spl5_27),
% 0.22/0.54    inference(avatar_split_clause,[],[f474,f253,f249])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    spl5_26 <=> r2_hidden(sK3(sK2,sK1),sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    spl5_27 <=> r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.54  fof(f474,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK2,sK1),sK2) | spl5_27),
% 0.22/0.54    inference(resolution,[],[f255,f131])).
% 0.22/0.54  fof(f131,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.22/0.54    inference(resolution,[],[f73,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(rectify,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    r1_tarski(sK2,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(resolution,[],[f25,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.54    inference(nnf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14,f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,k1_zfmisc_1(sK0))) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(nnf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(flattening,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.54    inference(negated_conjecture,[],[f6])).
% 0.22/0.54  fof(f6,conjecture,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(X0)) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0)) | spl5_27),
% 0.22/0.54    inference(avatar_component_clause,[],[f253])).
% 0.22/0.54  fof(f445,plain,(
% 0.22/0.54    spl5_1 | spl5_23),
% 0.22/0.54    inference(avatar_split_clause,[],[f402,f227,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    spl5_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.54  fof(f227,plain,(
% 0.22/0.54    spl5_23 <=> r2_hidden(sK3(sK1,sK2),sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.54  fof(f402,plain,(
% 0.22/0.54    r1_tarski(sK1,sK2) | spl5_23),
% 0.22/0.54    inference(resolution,[],[f229,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK1,sK2),sK1) | spl5_23),
% 0.22/0.54    inference(avatar_component_clause,[],[f227])).
% 0.22/0.54  fof(f439,plain,(
% 0.22/0.54    ~spl5_23 | spl5_24),
% 0.22/0.54    inference(avatar_split_clause,[],[f436,f231,f227])).
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    spl5_24 <=> r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.54  fof(f436,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK1,sK2),sK1) | spl5_24),
% 0.22/0.54    inference(resolution,[],[f233,f103])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.22/0.54    inference(resolution,[],[f61,f37])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.54    inference(resolution,[],[f24,f40])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f233,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | spl5_24),
% 0.22/0.54    inference(avatar_component_clause,[],[f231])).
% 0.22/0.54  fof(f420,plain,(
% 0.22/0.54    spl5_2 | spl5_26),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f414])).
% 0.22/0.54  fof(f414,plain,(
% 0.22/0.54    $false | (spl5_2 | spl5_26)),
% 0.22/0.54    inference(resolution,[],[f251,f88])).
% 0.22/0.54  fof(f88,plain,(
% 0.22/0.54    r2_hidden(sK3(sK2,sK1),sK2) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f56,f38])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ~r1_tarski(sK2,sK1) | spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    spl5_2 <=> r1_tarski(sK2,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.54  fof(f251,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK2,sK1),sK2) | spl5_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f249])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    ~spl5_26 | ~spl5_27 | spl5_2 | ~spl5_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f244,f99,f54,f253,f249])).
% 0.22/0.54  fof(f99,plain,(
% 0.22/0.54    spl5_7 <=> ! [X1] : (~r2_hidden(X1,sK2) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | r2_hidden(X1,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK2,sK1),k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK2,sK1),sK2) | (spl5_2 | ~spl5_7)),
% 0.22/0.54    inference(resolution,[],[f89,f100])).
% 0.22/0.54  fof(f100,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(X1,sK2)) ) | ~spl5_7),
% 0.22/0.54    inference(avatar_component_clause,[],[f99])).
% 0.22/0.54  fof(f89,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK2,sK1),sK1) | spl5_2),
% 0.22/0.54    inference(resolution,[],[f56,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f22])).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ~spl5_23 | ~spl5_24 | spl5_1 | ~spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f222,f84,f50,f231,f227])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    spl5_6 <=> ! [X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | r2_hidden(X1,sK2))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK1,sK2),k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK1,sK2),sK1) | (spl5_1 | ~spl5_6)),
% 0.22/0.54    inference(resolution,[],[f60,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X1] : (r2_hidden(X1,sK2) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | ~r2_hidden(X1,sK1)) ) | ~spl5_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f84])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ~r2_hidden(sK3(sK1,sK2),sK2) | spl5_1),
% 0.22/0.54    inference(resolution,[],[f52,f39])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ~r1_tarski(sK1,sK2) | spl5_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f50])).
% 0.22/0.54  fof(f101,plain,(
% 0.22/0.54    spl5_5 | spl5_7),
% 0.22/0.54    inference(avatar_split_clause,[],[f91,f99,f80])).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    spl5_5 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | r2_hidden(X1,sK1) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.54    inference(resolution,[],[f27,f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(nnf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ~spl5_5),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    $false | ~spl5_5),
% 0.22/0.54    inference(resolution,[],[f82,f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f80])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    spl5_5 | spl5_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f77,f84,f80])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X1] : (~r2_hidden(X1,sK1) | r2_hidden(X1,sK2) | ~r2_hidden(X1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))) )),
% 0.22/0.54    inference(resolution,[],[f26,f31])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f48,f54,f50])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ~r1_tarski(sK2,sK1) | ~r1_tarski(sK1,sK2)),
% 0.22/0.54    inference(resolution,[],[f45,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0,X1] : (sQ4_eqProxy(X0,X1) | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f36,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(flattening,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ~sQ4_eqProxy(sK1,sK2)),
% 0.22/0.54    inference(equality_proxy_replacement,[],[f28,f44])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    sK1 != sK2),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (1317)------------------------------
% 0.22/0.54  % (1317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1317)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (1317)Memory used [KB]: 6396
% 0.22/0.54  % (1317)Time elapsed: 0.114 s
% 0.22/0.54  % (1317)------------------------------
% 0.22/0.54  % (1317)------------------------------
% 0.22/0.54  % (1305)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (1301)Success in time 0.17 s
%------------------------------------------------------------------------------
