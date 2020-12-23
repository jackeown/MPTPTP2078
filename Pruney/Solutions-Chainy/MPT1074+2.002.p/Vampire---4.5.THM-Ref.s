%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 228 expanded)
%              Number of leaves         :   31 (  98 expanded)
%              Depth                    :   10
%              Number of atoms          :  474 (1047 expanded)
%              Number of equality atoms :   75 ( 105 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f113,f117,f121,f129,f153,f161,f164,f172,f212,f225,f241,f303,f310,f319,f338,f341])).

fof(f341,plain,
    ( spl5_12
    | ~ spl5_33 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | spl5_12
    | ~ spl5_33 ),
    inference(resolution,[],[f328,f165])).

fof(f165,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl5_12 ),
    inference(resolution,[],[f160,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f160,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl5_12
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl5_33
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f338,plain,
    ( spl5_33
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f337,f317,f308,f301,f327])).

fof(f301,plain,
    ( spl5_30
  <=> ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f308,plain,
    ( spl5_31
  <=> ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f317,plain,
    ( spl5_32
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f337,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(duplicate_literal_removal,[],[f335])).

fof(f335,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_30
    | ~ spl5_31
    | ~ spl5_32 ),
    inference(resolution,[],[f321,f309])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f321,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_30
    | ~ spl5_32 ),
    inference(resolution,[],[f320,f302])).

fof(f302,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f301])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_32 ),
    inference(resolution,[],[f318,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f318,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f317])).

fof(f319,plain,
    ( spl5_6
    | ~ spl5_3
    | ~ spl5_2
    | spl5_32
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f313,f119,f317,f111,f115,f127])).

fof(f127,plain,
    ( spl5_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f115,plain,
    ( spl5_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f111,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f119,plain,
    ( spl5_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f313,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | v1_xboole_0(sK1) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f312])).

fof(f312,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl5_4 ),
    inference(superposition,[],[f57,f311])).

fof(f311,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_2(sK3,X1,X2)
        | ~ m1_subset_1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f92,f120])).

fof(f120,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f57,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
      | ~ m1_subset_1(X4,sK1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                  | ~ m1_subset_1(X4,sK1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
              & v1_funct_2(X3,sK1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK1,X2,X3),sK0)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0)
                | ~ m1_subset_1(X4,sK1) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
            & v1_funct_2(X3,sK1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
              | ~ m1_subset_1(X4,sK1) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X3),sK0)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0)
            | ~ m1_subset_1(X4,sK1) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
          | ~ m1_subset_1(X4,sK1) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f310,plain,
    ( ~ spl5_11
    | spl5_31
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f306,f238,f119,f308,f156])).

fof(f156,plain,
    ( spl5_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f238,plain,
    ( spl5_22
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f306,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f305,f239])).

fof(f239,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(forward_demodulation,[],[f304,f239])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl5_4 ),
    inference(resolution,[],[f100,f120])).

fof(f100,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
        & r2_hidden(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f303,plain,
    ( ~ spl5_11
    | ~ spl5_4
    | spl5_30
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f299,f238,f301,f119,f156])).

fof(f299,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_22 ),
    inference(superposition,[],[f101,f239])).

fof(f101,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f241,plain,
    ( ~ spl5_2
    | spl5_22
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f236,f210,f238,f111])).

fof(f210,plain,
    ( spl5_18
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f236,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_18 ),
    inference(superposition,[],[f75,f211])).

fof(f211,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f210])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f225,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f223,f207,f111,f170])).

fof(f170,plain,
    ( spl5_13
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f207,plain,
    ( spl5_17
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f223,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f215,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f215,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl5_2
    | ~ spl5_17 ),
    inference(superposition,[],[f112,f208])).

fof(f208,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f207])).

fof(f112,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f212,plain,
    ( ~ spl5_2
    | spl5_17
    | spl5_18
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f202,f115,f210,f207,f111])).

fof(f202,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_3 ),
    inference(resolution,[],[f78,f116])).

fof(f116,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f172,plain,
    ( ~ spl5_13
    | spl5_12 ),
    inference(avatar_split_clause,[],[f168,f159,f170])).

fof(f168,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl5_12 ),
    inference(superposition,[],[f165,f94])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f164,plain,
    ( ~ spl5_2
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl5_2
    | spl5_11 ),
    inference(subsumption_resolution,[],[f112,f162])).

fof(f162,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_11 ),
    inference(resolution,[],[f157,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f157,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f161,plain,
    ( ~ spl5_11
    | ~ spl5_12
    | spl5_10 ),
    inference(avatar_split_clause,[],[f154,f151,f159,f156])).

fof(f151,plain,
    ( spl5_10
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f154,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl5_10 ),
    inference(resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f152,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f153,plain,
    ( ~ spl5_2
    | ~ spl5_10
    | spl5_1 ),
    inference(avatar_split_clause,[],[f148,f107,f151,f111])).

fof(f107,plain,
    ( spl5_1
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f148,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_1 ),
    inference(superposition,[],[f108,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f108,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f129,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f52,f127])).

fof(f52,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f55,f115])).

fof(f55,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f56,f111])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f58,f107])).

fof(f58,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:09:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (24838)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (24846)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.52  % (24848)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.52  % (24847)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.52  % (24840)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  % (24839)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.53  % (24839)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f349,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f109,f113,f117,f121,f129,f153,f161,f164,f172,f212,f225,f241,f303,f310,f319,f338,f341])).
% 0.20/0.54  fof(f341,plain,(
% 0.20/0.54    spl5_12 | ~spl5_33),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f340])).
% 0.20/0.54  fof(f340,plain,(
% 0.20/0.54    $false | (spl5_12 | ~spl5_33)),
% 0.20/0.54    inference(resolution,[],[f328,f165])).
% 0.20/0.54  fof(f165,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl5_12),
% 0.20/0.54    inference(resolution,[],[f160,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.54  fof(f160,plain,(
% 0.20/0.54    ~v5_relat_1(sK3,sK0) | spl5_12),
% 0.20/0.54    inference(avatar_component_clause,[],[f159])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    spl5_12 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.54  fof(f328,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_33),
% 0.20/0.54    inference(avatar_component_clause,[],[f327])).
% 0.20/0.54  fof(f327,plain,(
% 0.20/0.54    spl5_33 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.20/0.54  fof(f338,plain,(
% 0.20/0.54    spl5_33 | ~spl5_30 | ~spl5_31 | ~spl5_32),
% 0.20/0.54    inference(avatar_split_clause,[],[f337,f317,f308,f301,f327])).
% 0.20/0.54  fof(f301,plain,(
% 0.20/0.54    spl5_30 <=> ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.20/0.54  fof(f308,plain,(
% 0.20/0.54    spl5_31 <=> ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.20/0.54  fof(f317,plain,(
% 0.20/0.54    spl5_32 <=> ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.54  fof(f337,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_30 | ~spl5_31 | ~spl5_32)),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f335])).
% 0.20/0.54  fof(f335,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_30 | ~spl5_31 | ~spl5_32)),
% 0.20/0.54    inference(resolution,[],[f321,f309])).
% 0.20/0.54  fof(f309,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_31),
% 0.20/0.54    inference(avatar_component_clause,[],[f308])).
% 0.20/0.54  fof(f321,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl5_30 | ~spl5_32)),
% 0.20/0.54    inference(resolution,[],[f320,f302])).
% 0.20/0.54  fof(f302,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl5_30),
% 0.20/0.54    inference(avatar_component_clause,[],[f301])).
% 0.20/0.54  fof(f320,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_32),
% 0.20/0.54    inference(resolution,[],[f318,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.54  fof(f318,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_32),
% 0.20/0.54    inference(avatar_component_clause,[],[f317])).
% 0.20/0.54  fof(f319,plain,(
% 0.20/0.54    spl5_6 | ~spl5_3 | ~spl5_2 | spl5_32 | ~spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f313,f119,f317,f111,f115,f127])).
% 0.20/0.54  fof(f127,plain,(
% 0.20/0.54    spl5_6 <=> v1_xboole_0(sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.54  fof(f115,plain,(
% 0.20/0.54    spl5_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.54  fof(f119,plain,(
% 0.20/0.54    spl5_4 <=> v1_funct_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.54  fof(f313,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | v1_xboole_0(sK1)) ) | ~spl5_4),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f312])).
% 0.20/0.54  fof(f312,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | ~spl5_4),
% 0.20/0.54    inference(superposition,[],[f57,f311])).
% 0.20/0.54  fof(f311,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k3_funct_2(X1,X2,sK3,X0) = k1_funct_1(sK3,X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(sK3,X1,X2) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) ) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f92,f120])).
% 0.20/0.54  fof(f120,plain,(
% 0.20/0.54    v1_funct_1(sK3) | ~spl5_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f119])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.54    inference(flattening,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ((~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f43,f42,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK1,X2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,X2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) & v1_funct_2(X3,sK1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ? [X3] : (~r1_tarski(k2_relset_1(sK1,sK2,X3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,X3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) & ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.54    inference(flattening,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f16])).
% 0.20/0.54  fof(f16,conjecture,(
% 0.20/0.54    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.54  fof(f310,plain,(
% 0.20/0.54    ~spl5_11 | spl5_31 | ~spl5_4 | ~spl5_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f306,f238,f119,f308,f156])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    spl5_11 <=> v1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.54  fof(f238,plain,(
% 0.20/0.54    spl5_22 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.54  fof(f306,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_22)),
% 0.20/0.54    inference(forward_demodulation,[],[f305,f239])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    sK1 = k1_relat_1(sK3) | ~spl5_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f238])).
% 0.20/0.54  fof(f305,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | (~spl5_4 | ~spl5_22)),
% 0.20/0.54    inference(forward_demodulation,[],[f304,f239])).
% 0.20/0.54  fof(f304,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK4(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) | ~v1_relat_1(sK3)) ) | ~spl5_4),
% 0.20/0.54    inference(resolution,[],[f100,f120])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(equality_resolution,[],[f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f51])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f50])).
% 0.20/0.54  fof(f50,plain,(
% 0.20/0.54    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) & r2_hidden(sK4(X0,X1,X2),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.54    inference(flattening,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  fof(f15,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.54  fof(f303,plain,(
% 0.20/0.54    ~spl5_11 | ~spl5_4 | spl5_30 | ~spl5_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f299,f238,f301,f119,f156])).
% 0.20/0.54  fof(f299,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK4(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl5_22),
% 0.20/0.54    inference(superposition,[],[f101,f239])).
% 0.20/0.54  fof(f101,plain,(
% 0.20/0.54    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(equality_resolution,[],[f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK4(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f51])).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    ~spl5_2 | spl5_22 | ~spl5_18),
% 0.20/0.54    inference(avatar_split_clause,[],[f236,f210,f238,f111])).
% 0.20/0.54  fof(f210,plain,(
% 0.20/0.54    spl5_18 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.54  fof(f236,plain,(
% 0.20/0.54    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_18),
% 0.20/0.54    inference(superposition,[],[f75,f211])).
% 0.20/0.54  fof(f211,plain,(
% 0.20/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_18),
% 0.20/0.54    inference(avatar_component_clause,[],[f210])).
% 0.20/0.54  fof(f75,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f225,plain,(
% 0.20/0.54    spl5_13 | ~spl5_2 | ~spl5_17),
% 0.20/0.54    inference(avatar_split_clause,[],[f223,f207,f111,f170])).
% 0.20/0.54  fof(f170,plain,(
% 0.20/0.54    spl5_13 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.20/0.54  fof(f207,plain,(
% 0.20/0.54    spl5_17 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.54  fof(f223,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_2 | ~spl5_17)),
% 0.20/0.54    inference(forward_demodulation,[],[f215,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.54    inference(equality_resolution,[],[f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.54    inference(flattening,[],[f47])).
% 0.20/0.54  fof(f47,plain,(
% 0.20/0.54    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.54  fof(f215,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl5_2 | ~spl5_17)),
% 0.20/0.54    inference(superposition,[],[f112,f208])).
% 0.20/0.54  fof(f208,plain,(
% 0.20/0.54    k1_xboole_0 = sK2 | ~spl5_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f207])).
% 0.20/0.54  fof(f112,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f111])).
% 0.20/0.54  fof(f212,plain,(
% 0.20/0.54    ~spl5_2 | spl5_17 | spl5_18 | ~spl5_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f202,f115,f210,f207,f111])).
% 0.20/0.54  fof(f202,plain,(
% 0.20/0.54    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_3),
% 0.20/0.54    inference(resolution,[],[f78,f116])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    v1_funct_2(sK3,sK1,sK2) | ~spl5_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f115])).
% 0.20/0.54  fof(f78,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f49])).
% 0.20/0.54  fof(f49,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f172,plain,(
% 0.20/0.54    ~spl5_13 | spl5_12),
% 0.20/0.54    inference(avatar_split_clause,[],[f168,f159,f170])).
% 0.20/0.54  fof(f168,plain,(
% 0.20/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl5_12),
% 0.20/0.54    inference(superposition,[],[f165,f94])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f48])).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    ~spl5_2 | spl5_11),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f163])).
% 0.20/0.54  fof(f163,plain,(
% 0.20/0.54    $false | (~spl5_2 | spl5_11)),
% 0.20/0.54    inference(subsumption_resolution,[],[f112,f162])).
% 0.20/0.54  fof(f162,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_11),
% 0.20/0.54    inference(resolution,[],[f157,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ~v1_relat_1(sK3) | spl5_11),
% 0.20/0.54    inference(avatar_component_clause,[],[f156])).
% 0.20/0.54  fof(f161,plain,(
% 0.20/0.54    ~spl5_11 | ~spl5_12 | spl5_10),
% 0.20/0.54    inference(avatar_split_clause,[],[f154,f151,f159,f156])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    spl5_10 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.54  fof(f154,plain,(
% 0.20/0.54    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl5_10),
% 0.20/0.54    inference(resolution,[],[f152,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f45])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.54  fof(f152,plain,(
% 0.20/0.54    ~r1_tarski(k2_relat_1(sK3),sK0) | spl5_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f151])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    ~spl5_2 | ~spl5_10 | spl5_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f148,f107,f151,f111])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    spl5_1 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.54  fof(f148,plain,(
% 0.20/0.54    ~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | spl5_1),
% 0.20/0.54    inference(superposition,[],[f108,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f107])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ~spl5_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f52,f127])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ~v1_xboole_0(sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f121,plain,(
% 0.20/0.54    spl5_4),
% 0.20/0.54    inference(avatar_split_clause,[],[f54,f119])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    v1_funct_1(sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    spl5_3),
% 0.20/0.54    inference(avatar_split_clause,[],[f55,f115])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    spl5_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f56,f111])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ~spl5_1),
% 0.20/0.54    inference(avatar_split_clause,[],[f58,f107])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f44])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (24839)------------------------------
% 0.20/0.54  % (24839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24839)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (24839)Memory used [KB]: 10874
% 0.20/0.54  % (24839)Time elapsed: 0.082 s
% 0.20/0.54  % (24839)------------------------------
% 0.20/0.54  % (24839)------------------------------
% 0.20/0.55  % (24832)Success in time 0.181 s
%------------------------------------------------------------------------------
