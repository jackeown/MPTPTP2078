%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0717+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 146 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 ( 550 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f114,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f59,f63,f67,f71,f84,f90,f95,f98,f105,f113])).

fof(f113,plain,
    ( spl6_1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f110,f103,f79,f65,f53])).

fof(f53,plain,
    ( spl6_1
  <=> r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f65,plain,
    ( spl6_4
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f79,plain,
    ( spl6_6
  <=> ! [X1,X2] :
        ( r2_hidden(X1,X2)
        | ~ v5_relat_1(sK1,X2)
        | ~ m1_subset_1(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f103,plain,
    ( spl6_10
  <=> m1_subset_1(k1_funct_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f110,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | r2_hidden(k1_funct_1(sK1,sK2),sK0)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(resolution,[],[f104,f80])).

fof(f80,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,X2)
        | ~ v5_relat_1(sK1,X2)
        | r2_hidden(X1,X2) )
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f104,plain,
    ( m1_subset_1(k1_funct_1(sK1,sK2),sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl6_10
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f100,f93,f69,f65,f103])).

fof(f69,plain,
    ( spl6_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f93,plain,
    ( spl6_9
  <=> r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f100,plain,
    ( m1_subset_1(k1_funct_1(sK1,sK2),sK0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f97,f66])).

fof(f66,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK1,X0)
        | m1_subset_1(k1_funct_1(sK1,sK2),X0) )
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(resolution,[],[f94,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | m1_subset_1(X0,X1)
        | ~ v5_relat_1(sK1,X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f46,f73])).

fof(f73,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(X0))
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f72,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(sK1),X0)
        | ~ v5_relat_1(sK1,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f41,f70])).

fof(f70,plain,
    ( v1_relat_1(sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f94,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f98,plain,
    ( ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f94,f83])).

fof(f83,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_7
  <=> ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f95,plain,
    ( spl6_9
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f91,f88,f57,f93])).

fof(f57,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f88,plain,
    ( spl6_8
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f91,plain,
    ( r2_hidden(k1_funct_1(sK1,sK2),k2_relat_1(sK1))
    | ~ spl6_2
    | ~ spl6_8 ),
    inference(resolution,[],[f89,f58])).

fof(f58,plain,
    ( r2_hidden(sK2,k1_relat_1(sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1)) )
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f90,plain,
    ( ~ spl6_5
    | spl6_8
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f85,f61,f88,f69])).

fof(f61,plain,
    ( spl6_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | r2_hidden(k1_funct_1(sK1,X0),k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f49,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f26,f25,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f84,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f77,f69,f82,f79])).

fof(f77,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK1))
        | r2_hidden(X1,X2)
        | ~ m1_subset_1(X1,X2)
        | ~ v5_relat_1(sK1,X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f75,f73])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f47,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f71,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
    & r2_hidden(sK2,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
            & r2_hidden(X2,k1_relat_1(X1)) )
        & v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
          & r2_hidden(X2,k1_relat_1(sK1)) )
      & v1_funct_1(sK1)
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X2] :
        ( ~ r2_hidden(k1_funct_1(sK1,X2),sK0)
        & r2_hidden(X2,k1_relat_1(sK1)) )
   => ( ~ r2_hidden(k1_funct_1(sK1,sK2),sK0)
      & r2_hidden(sK2,k1_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),X0)
          & r2_hidden(X2,k1_relat_1(X1)) )
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k1_relat_1(X1))
           => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f67,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f31,f65])).

fof(f31,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f32,f61])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f33,f57])).

fof(f33,plain,(
    r2_hidden(sK2,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f53])).

fof(f34,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f21])).

%------------------------------------------------------------------------------
