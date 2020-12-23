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
% DateTime   : Thu Dec  3 13:17:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 296 expanded)
%              Number of leaves         :   36 ( 122 expanded)
%              Depth                    :   13
%              Number of atoms          :  593 (1360 expanded)
%              Number of equality atoms :   33 (  39 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f422,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f98,f102,f106,f205,f221,f226,f234,f241,f245,f252,f262,f295,f298,f372,f417])).

fof(f417,plain,
    ( spl8_27
    | ~ spl8_6
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f414,f239,f104,f80,f96,f243])).

fof(f243,plain,
    ( spl8_27
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f96,plain,
    ( spl8_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f80,plain,
    ( spl8_2
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f104,plain,
    ( spl8_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f239,plain,
    ( spl8_26
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ l1_struct_0(X1)
        | ~ r1_tsep_1(sK2,X1)
        | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f414,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_2
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(resolution,[],[f413,f81])).

fof(f81,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(sK2,X0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) )
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,
    ( ! [X0] :
        ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tsep_1(sK2,X0) )
    | ~ spl8_8
    | ~ spl8_26 ),
    inference(resolution,[],[f389,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1)
        | ~ r1_tsep_1(sK2,X0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f381,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f381,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ r1_tsep_1(sK2,X0)
        | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl8_26 ),
    inference(resolution,[],[f240,f57])).

fof(f57,plain,(
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

fof(f240,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ r1_tsep_1(sK2,X1)
        | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f239])).

fof(f372,plain,
    ( spl8_34
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f369,f260,f286])).

fof(f286,plain,
    ( spl8_34
  <=> v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f260,plain,
    ( spl8_30
  <=> r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f369,plain,
    ( v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))
    | ~ spl8_30 ),
    inference(resolution,[],[f265,f70])).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ? [X1] : r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
     => v1_xboole_0(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f265,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))
    | ~ spl8_30 ),
    inference(resolution,[],[f261,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f261,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f260])).

fof(f298,plain,
    ( spl8_7
    | ~ spl8_19
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f296,f293,f195,f100])).

fof(f100,plain,
    ( spl8_7
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f195,plain,
    ( spl8_19
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f293,plain,
    ( spl8_35
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f296,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl8_35 ),
    inference(resolution,[],[f294,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f69,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f294,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f293])).

fof(f295,plain,
    ( ~ spl8_3
    | ~ spl8_24
    | ~ spl8_21
    | spl8_35
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f290,f286,f293,f203,f219,f84])).

fof(f84,plain,
    ( spl8_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f219,plain,
    ( spl8_24
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f203,plain,
    ( spl8_21
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f290,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ spl8_34 ),
    inference(superposition,[],[f287,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) = k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f58,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f40,f39,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK3(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK4(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f287,plain,
    ( v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f286])).

fof(f262,plain,
    ( ~ spl8_22
    | spl8_30
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f258,f250,f260,f211])).

fof(f211,plain,
    ( spl8_22
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f250,plain,
    ( spl8_28
  <=> r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f258,plain,
    ( r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))
    | ~ l1_struct_0(sK2)
    | ~ spl8_28 ),
    inference(superposition,[],[f251,f54])).

fof(f251,plain,
    ( r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f250])).

fof(f252,plain,
    ( ~ spl8_19
    | spl8_28
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f247,f243,f250,f195])).

fof(f247,plain,
    ( r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl8_27 ),
    inference(superposition,[],[f244,f54])).

fof(f244,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl8_27
    | ~ spl8_6
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f237,f104,f88,f77,f96,f243])).

fof(f77,plain,
    ( spl8_1
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f88,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f237,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_1
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f180,f78])).

fof(f78,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ r1_tsep_1(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f177,f89])).

fof(f89,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_xboole_0(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,sK0)
        | ~ r1_tsep_1(X1,X0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f174,f105])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(X2)
        | ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X0,X2)
        | ~ r1_tsep_1(X0,X1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f150,f105])).

fof(f150,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ l1_pre_topc(X4)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X3,X4)
      | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X5)
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f117,f68])).

fof(f117,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_pre_topc(X1)
      | r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X3)
      | ~ l1_pre_topc(X3) ) ),
    inference(resolution,[],[f115,f68])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f113,f57])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f241,plain,
    ( ~ spl8_22
    | spl8_26
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f236,f104,f88,f239,f211])).

fof(f236,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2))
        | ~ r1_tsep_1(sK2,X1)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(sK2) )
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(resolution,[],[f180,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f234,plain,
    ( ~ spl8_8
    | ~ spl8_4
    | spl8_24 ),
    inference(avatar_split_clause,[],[f231,f219,f88,f104])).

fof(f231,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_4
    | spl8_24 ),
    inference(resolution,[],[f222,f89])).

fof(f222,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_24 ),
    inference(resolution,[],[f220,f68])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f226,plain,
    ( ~ spl8_6
    | ~ spl8_8
    | spl8_21 ),
    inference(avatar_split_clause,[],[f223,f203,f104,f96])).

fof(f223,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_8
    | spl8_21 ),
    inference(resolution,[],[f206,f105])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl8_21 ),
    inference(resolution,[],[f204,f68])).

fof(f204,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f221,plain,
    ( ~ spl8_24
    | spl8_22 ),
    inference(avatar_split_clause,[],[f217,f211,f219])).

fof(f217,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_22 ),
    inference(resolution,[],[f212,f57])).

fof(f212,plain,
    ( ~ l1_struct_0(sK2)
    | spl8_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f205,plain,
    ( ~ spl8_21
    | spl8_19 ),
    inference(avatar_split_clause,[],[f201,f195,f203])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_19 ),
    inference(resolution,[],[f196,f57])).

fof(f196,plain,
    ( ~ l1_struct_0(sK1)
    | spl8_19 ),
    inference(avatar_component_clause,[],[f195])).

fof(f106,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f47,f104])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_tsep_1(X2,X1)
              | r1_tsep_1(X1,X2) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_tsep_1(X2,sK1)
            | r1_tsep_1(sK1,X2) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ( r1_tsep_1(X2,sK1)
          | r1_tsep_1(sK1,X2) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( r1_tsep_1(sK2,sK1)
        | r1_tsep_1(sK1,sK2) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
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
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f102,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f48,f100])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f98,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f49,f96])).

fof(f49,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f52,f84])).

fof(f52,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f82,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f53,f80,f77])).

fof(f53,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:02:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (21896)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (21895)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (21896)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (21904)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (21903)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (21894)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (21891)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21891)Refutation not found, incomplete strategy% (21891)------------------------------
% 0.20/0.49  % (21891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21891)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21891)Memory used [KB]: 10618
% 0.20/0.49  % (21891)Time elapsed: 0.082 s
% 0.20/0.49  % (21891)------------------------------
% 0.20/0.49  % (21891)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f82,f86,f90,f98,f102,f106,f205,f221,f226,f234,f241,f245,f252,f262,f295,f298,f372,f417])).
% 0.20/0.49  fof(f417,plain,(
% 0.20/0.49    spl8_27 | ~spl8_6 | ~spl8_2 | ~spl8_8 | ~spl8_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f414,f239,f104,f80,f96,f243])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    spl8_27 <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl8_6 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    spl8_2 <=> r1_tsep_1(sK2,sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl8_8 <=> l1_pre_topc(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.50  fof(f239,plain,(
% 0.20/0.50    spl8_26 <=> ! [X1] : (~m1_pre_topc(X1,sK0) | ~l1_struct_0(X1) | ~r1_tsep_1(sK2,X1) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.20/0.50  fof(f414,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl8_2 | ~spl8_8 | ~spl8_26)),
% 0.20/0.50    inference(resolution,[],[f413,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK1) | ~spl8_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f413,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tsep_1(sK2,X0) | ~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))) ) | (~spl8_8 | ~spl8_26)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f411])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,sK0) | ~r1_tsep_1(sK2,X0)) ) | (~spl8_8 | ~spl8_26)),
% 0.20/0.50    inference(resolution,[],[f389,f105])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    l1_pre_topc(sK0) | ~spl8_8),
% 0.20/0.50    inference(avatar_component_clause,[],[f104])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1) | ~r1_tsep_1(sK2,X0)) ) | ~spl8_26),
% 0.20/0.50    inference(resolution,[],[f381,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.50  fof(f381,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~r1_tsep_1(sK2,X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) | ~m1_pre_topc(X0,sK0)) ) | ~spl8_26),
% 0.20/0.50    inference(resolution,[],[f240,f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    ( ! [X1] : (~l1_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~r1_tsep_1(sK2,X1) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2))) ) | ~spl8_26),
% 0.20/0.50    inference(avatar_component_clause,[],[f239])).
% 0.20/0.50  fof(f372,plain,(
% 0.20/0.50    spl8_34 | ~spl8_30),
% 0.20/0.50    inference(avatar_split_clause,[],[f369,f260,f286])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    spl8_34 <=> v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 0.20/0.50  fof(f260,plain,(
% 0.20/0.50    spl8_30 <=> r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 0.20/0.50  fof(f369,plain,(
% 0.20/0.50    v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))) | ~spl8_30),
% 0.20/0.50    inference(resolution,[],[f265,f70])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f25,f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) => v1_xboole_0(X0))),
% 0.20/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)))) ) | ~spl8_30),
% 0.20/0.50    inference(resolution,[],[f261,f72])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f26,f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,plain,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    inference(rectify,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) | ~spl8_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f260])).
% 0.20/0.50  fof(f298,plain,(
% 0.20/0.50    spl8_7 | ~spl8_19 | ~spl8_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f296,f293,f195,f100])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl8_7 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    spl8_19 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.20/0.50  fof(f293,plain,(
% 0.20/0.50    spl8_35 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl8_35),
% 0.20/0.50    inference(resolution,[],[f294,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f111])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(superposition,[],[f69,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    v1_xboole_0(k2_struct_0(sK1)) | ~spl8_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f293])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    ~spl8_3 | ~spl8_24 | ~spl8_21 | spl8_35 | ~spl8_34),
% 0.20/0.50    inference(avatar_split_clause,[],[f290,f286,f293,f203,f219,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    spl8_3 <=> m1_pre_topc(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.50  fof(f219,plain,(
% 0.20/0.50    spl8_24 <=> l1_pre_topc(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    spl8_21 <=> l1_pre_topc(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.20/0.50  fof(f290,plain,(
% 0.20/0.50    v1_xboole_0(k2_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK2) | ~m1_pre_topc(sK1,sK2) | ~spl8_34),
% 0.20/0.50    inference(superposition,[],[f287,f114])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_struct_0(X0) = k3_xboole_0(k2_struct_0(X0),k2_struct_0(X1)) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.20/0.50    inference(resolution,[],[f58,f73])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1))) & ((sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1)) & r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f37,f40,f39,f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK3(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK3(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK3(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK3(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) = k9_subset_1(u1_struct_0(X1),sK4(X0,X1),k2_struct_0(X1)) & r2_hidden(sK4(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK5(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(rectify,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    v1_xboole_0(k3_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2))) | ~spl8_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f286])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    ~spl8_22 | spl8_30 | ~spl8_28),
% 0.20/0.50    inference(avatar_split_clause,[],[f258,f250,f260,f211])).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    spl8_22 <=> l1_struct_0(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.20/0.50  fof(f250,plain,(
% 0.20/0.50    spl8_28 <=> r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK2)) | ~l1_struct_0(sK2) | ~spl8_28),
% 0.20/0.50    inference(superposition,[],[f251,f54])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_28),
% 0.20/0.50    inference(avatar_component_clause,[],[f250])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    ~spl8_19 | spl8_28 | ~spl8_27),
% 0.20/0.50    inference(avatar_split_clause,[],[f247,f243,f250,f195])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    r1_xboole_0(k2_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1) | ~spl8_27),
% 0.20/0.50    inference(superposition,[],[f244,f54])).
% 0.20/0.50  fof(f244,plain,(
% 0.20/0.50    r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f243])).
% 0.20/0.50  fof(f245,plain,(
% 0.20/0.50    spl8_27 | ~spl8_6 | ~spl8_1 | ~spl8_4 | ~spl8_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f237,f104,f88,f77,f96,f243])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl8_1 <=> r1_tsep_1(sK1,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl8_1 | ~spl8_4 | ~spl8_8)),
% 0.20/0.50    inference(resolution,[],[f180,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    r1_tsep_1(sK1,sK2) | ~spl8_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X1] : (~r1_tsep_1(X1,sK2) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2))) ) | (~spl8_4 | ~spl8_8)),
% 0.20/0.50    inference(resolution,[],[f177,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f88])).
% 0.20/0.50  fof(f177,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_pre_topc(X0,sK0) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,sK0) | ~r1_tsep_1(X1,X0)) ) | ~spl8_8),
% 0.20/0.50    inference(resolution,[],[f174,f105])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X2) | ~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X0,X2) | ~r1_tsep_1(X0,X1)) ) | ~spl8_8),
% 0.20/0.50    inference(resolution,[],[f150,f105])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ( ! [X4,X2,X5,X3] : (~l1_pre_topc(X4) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X3,X4) | r1_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) | ~m1_pre_topc(X2,X5) | ~l1_pre_topc(X5)) )),
% 0.20/0.50    inference(resolution,[],[f117,f68])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ( ! [X2,X3,X1] : (~l1_pre_topc(X1) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X3) | ~l1_pre_topc(X3)) )),
% 0.20/0.50    inference(resolution,[],[f115,f68])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0)) )),
% 0.20/0.50    inference(resolution,[],[f113,f57])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_pre_topc(X1)) )),
% 0.20/0.50    inference(resolution,[],[f55,f57])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    ~spl8_22 | spl8_26 | ~spl8_4 | ~spl8_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f236,f104,f88,f239,f211])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_pre_topc(X1,sK0) | r1_xboole_0(u1_struct_0(X1),u1_struct_0(sK2)) | ~r1_tsep_1(sK2,X1) | ~l1_struct_0(X1) | ~l1_struct_0(sK2)) ) | (~spl8_4 | ~spl8_8)),
% 0.20/0.50    inference(resolution,[],[f180,f74])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    ~spl8_8 | ~spl8_4 | spl8_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f231,f219,f88,f104])).
% 0.20/0.50  fof(f231,plain,(
% 0.20/0.50    ~l1_pre_topc(sK0) | (~spl8_4 | spl8_24)),
% 0.20/0.50    inference(resolution,[],[f222,f89])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0)) ) | spl8_24),
% 0.20/0.50    inference(resolution,[],[f220,f68])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | spl8_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f219])).
% 0.20/0.50  fof(f226,plain,(
% 0.20/0.50    ~spl8_6 | ~spl8_8 | spl8_21),
% 0.20/0.50    inference(avatar_split_clause,[],[f223,f203,f104,f96])).
% 0.20/0.50  fof(f223,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | (~spl8_8 | spl8_21)),
% 0.20/0.50    inference(resolution,[],[f206,f105])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | spl8_21),
% 0.20/0.50    inference(resolution,[],[f204,f68])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | spl8_21),
% 0.20/0.50    inference(avatar_component_clause,[],[f203])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ~spl8_24 | spl8_22),
% 0.20/0.50    inference(avatar_split_clause,[],[f217,f211,f219])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ~l1_pre_topc(sK2) | spl8_22),
% 0.20/0.50    inference(resolution,[],[f212,f57])).
% 0.20/0.50  fof(f212,plain,(
% 0.20/0.50    ~l1_struct_0(sK2) | spl8_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f211])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    ~spl8_21 | spl8_19),
% 0.20/0.50    inference(avatar_split_clause,[],[f201,f195,f203])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | spl8_19),
% 0.20/0.50    inference(resolution,[],[f196,f57])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~l1_struct_0(sK1) | spl8_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f195])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl8_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f47,f104])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    l1_pre_topc(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    (((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f32,f31,f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ? [X2] : ((r1_tsep_1(X2,sK1) | r1_tsep_1(sK1,X2)) & m1_pre_topc(sK1,X2) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => ((r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.50  fof(f12,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f11])).
% 0.20/0.50  fof(f11,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    ~spl8_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f48,f100])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl8_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f49,f96])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl8_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f88])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    m1_pre_topc(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl8_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f84])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    m1_pre_topc(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl8_1 | spl8_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f80,f77])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    r1_tsep_1(sK2,sK1) | r1_tsep_1(sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f33])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (21896)------------------------------
% 0.20/0.50  % (21896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21896)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (21896)Memory used [KB]: 10874
% 0.20/0.50  % (21896)Time elapsed: 0.060 s
% 0.20/0.50  % (21896)------------------------------
% 0.20/0.50  % (21896)------------------------------
% 0.20/0.50  % (21889)Success in time 0.137 s
%------------------------------------------------------------------------------
