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
% DateTime   : Thu Dec  3 13:01:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 161 expanded)
%              Number of leaves         :   26 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  334 ( 552 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f83,f103,f109,f115,f142,f157,f166,f387,f399,f411])).

fof(f411,plain,
    ( ~ spl9_12
    | ~ spl9_35 ),
    inference(avatar_contradiction_clause,[],[f410])).

fof(f410,plain,
    ( $false
    | ~ spl9_12
    | ~ spl9_35 ),
    inference(trivial_inequality_removal,[],[f401])).

fof(f401,plain,
    ( sK5 != sK5
    | ~ spl9_12
    | ~ spl9_35 ),
    inference(unit_resulting_resolution,[],[f396,f249])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK6)
        | sK5 != X0 )
    | ~ spl9_12 ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ sP0(X0,sK6)
        | sK5 != X0
        | ~ sP0(X0,sK6) )
    | ~ spl9_12 ),
    inference(resolution,[],[f247,f232])).

fof(f232,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK8(X0,sK6),sK3)
      | sK5 != X0
      | ~ sP0(X0,sK6) ) ),
    inference(superposition,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,sK8(X0,X1)) = X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK8(X0,X1)) = X0
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK8(X0,X1)) = X0
        & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f41,plain,(
    ! [X4] :
      ( sK5 != k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X4] :
        ( sK5 != k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f12,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( sK5 != k1_funct_1(sK6,X4)
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f247,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(X0,sK6),sK3)
        | ~ sP0(X0,sK6) )
    | ~ spl9_12 ),
    inference(resolution,[],[f246,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),k1_relat_1(X1))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f246,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,k1_relat_1(sK6))
        | r2_hidden(X4,sK3) )
    | ~ spl9_12 ),
    inference(resolution,[],[f56,f165])).

fof(f165,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl9_12
  <=> m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f396,plain,
    ( sP0(sK5,sK6)
    | ~ spl9_35 ),
    inference(avatar_component_clause,[],[f394])).

fof(f394,plain,
    ( spl9_35
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f399,plain,
    ( spl9_35
    | ~ spl9_8
    | ~ spl9_34 ),
    inference(avatar_split_clause,[],[f391,f384,f112,f394])).

fof(f112,plain,
    ( spl9_8
  <=> sP1(sK6,k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f384,plain,
    ( spl9_34
  <=> r2_hidden(sK5,k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f391,plain,
    ( sP0(sK5,sK6)
    | ~ spl9_8
    | ~ spl9_34 ),
    inference(resolution,[],[f386,f125])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK6))
        | sP0(X2,sK6) )
    | ~ spl9_8 ),
    inference(resolution,[],[f45,f114])).

fof(f114,plain,
    ( sP1(sK6,k2_relat_1(sK6))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X3,X1)
      | sP0(X3,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sP0(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sP0(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f386,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f384])).

fof(f387,plain,
    ( spl9_34
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f382,f70,f65,f384])).

fof(f65,plain,
    ( spl9_1
  <=> r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f70,plain,
    ( spl9_2
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f382,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f376,f72])).

fof(f72,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f376,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ spl9_1 ),
    inference(superposition,[],[f67,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f67,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f166,plain,
    ( spl9_12
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f159,f154,f163])).

fof(f154,plain,
    ( spl9_11
  <=> r1_tarski(k1_relat_1(sK6),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f159,plain,
    ( m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))
    | ~ spl9_11 ),
    inference(unit_resulting_resolution,[],[f156,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f156,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( spl9_11
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f152,f138,f98,f154])).

fof(f98,plain,
    ( spl9_6
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f138,plain,
    ( spl9_9
  <=> v4_relat_1(sK6,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f152,plain,
    ( r1_tarski(k1_relat_1(sK6),sK3)
    | ~ spl9_6
    | ~ spl9_9 ),
    inference(unit_resulting_resolution,[],[f100,f140,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f140,plain,
    ( v4_relat_1(sK6,sK3)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f138])).

fof(f100,plain,
    ( v1_relat_1(sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f142,plain,
    ( spl9_9
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f135,f70,f138])).

fof(f135,plain,
    ( v4_relat_1(sK6,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f60,f72])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,
    ( spl9_8
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f110,f106,f112])).

fof(f106,plain,
    ( spl9_7
  <=> sP2(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f110,plain,
    ( sP1(sK6,k2_relat_1(sK6))
    | ~ spl9_7 ),
    inference(unit_resulting_resolution,[],[f108,f62])).

fof(f62,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f108,plain,
    ( sP2(sK6)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f106])).

fof(f109,plain,
    ( spl9_7
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f104,f98,f80,f106])).

fof(f80,plain,
    ( spl9_4
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f104,plain,
    ( sP2(sK6)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(unit_resulting_resolution,[],[f82,f100,f52])).

fof(f52,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f15,f22,f21,f20])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f82,plain,
    ( v1_funct_1(sK6)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f103,plain,
    ( spl9_6
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f102,f70,f98])).

fof(f102,plain,
    ( v1_relat_1(sK6)
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f95,plain,
    ( v1_relat_1(sK6)
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | ~ spl9_2 ),
    inference(resolution,[],[f42,f72])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f83,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f39,f70])).

fof(f39,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f40,f65])).

fof(f40,plain,(
    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:11:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (21462)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (21470)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (21473)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (21465)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (21473)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (21463)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (21459)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f68,f73,f83,f103,f109,f115,f142,f157,f166,f387,f399,f411])).
% 0.22/0.50  fof(f411,plain,(
% 0.22/0.50    ~spl9_12 | ~spl9_35),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f410])).
% 0.22/0.50  fof(f410,plain,(
% 0.22/0.50    $false | (~spl9_12 | ~spl9_35)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f401])).
% 0.22/0.50  fof(f401,plain,(
% 0.22/0.50    sK5 != sK5 | (~spl9_12 | ~spl9_35)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f396,f249])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    ( ! [X0] : (~sP0(X0,sK6) | sK5 != X0) ) | ~spl9_12),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f248])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ( ! [X0] : (~sP0(X0,sK6) | sK5 != X0 | ~sP0(X0,sK6)) ) | ~spl9_12),
% 0.22/0.50    inference(resolution,[],[f247,f232])).
% 0.22/0.50  fof(f232,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(sK8(X0,sK6),sK3) | sK5 != X0 | ~sP0(X0,sK6)) )),
% 0.22/0.50    inference(superposition,[],[f41,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_funct_1(X1,sK8(X0,X1)) = X0 | ~sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f32,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK8(X0,X1)) = X0 & r2_hidden(sK8(X0,X1),k1_relat_1(X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X4] : (sK5 != k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X4] : (sK5 != k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f12,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK5 != k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK8(X0,sK6),sK3) | ~sP0(X0,sK6)) ) | ~spl9_12),
% 0.22/0.50    inference(resolution,[],[f246,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),k1_relat_1(X1)) | ~sP0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ( ! [X4] : (~r2_hidden(X4,k1_relat_1(sK6)) | r2_hidden(X4,sK3)) ) | ~spl9_12),
% 0.22/0.50    inference(resolution,[],[f56,f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) | ~spl9_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f163])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl9_12 <=> m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f396,plain,(
% 0.22/0.50    sP0(sK5,sK6) | ~spl9_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f394])).
% 0.22/0.50  fof(f394,plain,(
% 0.22/0.50    spl9_35 <=> sP0(sK5,sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    spl9_35 | ~spl9_8 | ~spl9_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f391,f384,f112,f394])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl9_8 <=> sP1(sK6,k2_relat_1(sK6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.22/0.50  fof(f384,plain,(
% 0.22/0.50    spl9_34 <=> r2_hidden(sK5,k2_relat_1(sK6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.22/0.50  fof(f391,plain,(
% 0.22/0.50    sP0(sK5,sK6) | (~spl9_8 | ~spl9_34)),
% 0.22/0.50    inference(resolution,[],[f386,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK6)) | sP0(X2,sK6)) ) | ~spl9_8),
% 0.22/0.50    inference(resolution,[],[f45,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    sP1(sK6,k2_relat_1(sK6)) | ~spl9_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~r2_hidden(X3,X1) | sP0(X3,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f28,f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK7(X0,X1),X0) | ~r2_hidden(sK7(X0,X1),X1)) & (sP0(sK7(X0,X1),X0) | r2_hidden(sK7(X0,X1),X1))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.22/0.50    inference(rectify,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f386,plain,(
% 0.22/0.50    r2_hidden(sK5,k2_relat_1(sK6)) | ~spl9_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f384])).
% 0.22/0.50  fof(f387,plain,(
% 0.22/0.50    spl9_34 | ~spl9_1 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f382,f70,f65,f384])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl9_1 <=> r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl9_2 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.50  fof(f382,plain,(
% 0.22/0.50    r2_hidden(sK5,k2_relat_1(sK6)) | (~spl9_1 | ~spl9_2)),
% 0.22/0.50    inference(subsumption_resolution,[],[f376,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl9_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f70])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    r2_hidden(sK5,k2_relat_1(sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~spl9_1),
% 0.22/0.50    inference(superposition,[],[f67,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) | ~spl9_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f65])).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    spl9_12 | ~spl9_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f154,f163])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    spl9_11 <=> r1_tarski(k1_relat_1(sK6),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    m1_subset_1(k1_relat_1(sK6),k1_zfmisc_1(sK3)) | ~spl9_11),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f156,f58])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK6),sK3) | ~spl9_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f154])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl9_11 | ~spl9_6 | ~spl9_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f138,f98,f154])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    spl9_6 <=> v1_relat_1(sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    spl9_9 <=> v4_relat_1(sK6,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    r1_tarski(k1_relat_1(sK6),sK3) | (~spl9_6 | ~spl9_9)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f100,f140,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    v4_relat_1(sK6,sK3) | ~spl9_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f138])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    v1_relat_1(sK6) | ~spl9_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f98])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    spl9_9 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f135,f70,f138])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    v4_relat_1(sK6,sK3) | ~spl9_2),
% 0.22/0.50    inference(resolution,[],[f60,f72])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl9_8 | ~spl9_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f110,f106,f112])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    spl9_7 <=> sP2(sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    sP1(sK6,k2_relat_1(sK6)) | ~spl9_7),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f108,f62])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    sP2(sK6) | ~spl9_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f106])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl9_7 | ~spl9_4 | ~spl9_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f104,f98,f80,f106])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl9_4 <=> v1_funct_1(sK6)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    sP2(sK6) | (~spl9_4 | ~spl9_6)),
% 0.22/0.50    inference(unit_resulting_resolution,[],[f82,f100,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(definition_folding,[],[f15,f22,f21,f20])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    v1_funct_1(sK6) | ~spl9_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl9_6 | ~spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f102,f70,f98])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v1_relat_1(sK6) | ~spl9_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f95,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    v1_relat_1(sK6) | ~v1_relat_1(k2_zfmisc_1(sK3,sK4)) | ~spl9_2),
% 0.22/0.50    inference(resolution,[],[f42,f72])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl9_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f80])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_funct_1(sK6)),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl9_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f70])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl9_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f40,f65])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (21473)------------------------------
% 0.22/0.50  % (21473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21473)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (21473)Memory used [KB]: 10874
% 0.22/0.50  % (21473)Time elapsed: 0.079 s
% 0.22/0.50  % (21473)------------------------------
% 0.22/0.50  % (21473)------------------------------
% 0.22/0.50  % (21471)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  % (21472)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (21456)Success in time 0.143 s
%------------------------------------------------------------------------------
