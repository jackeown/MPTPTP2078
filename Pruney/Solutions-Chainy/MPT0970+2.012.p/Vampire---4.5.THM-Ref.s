%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:50 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  235 (1089 expanded)
%              Number of leaves         :   33 ( 355 expanded)
%              Depth                    :   17
%              Number of atoms          :  855 (5490 expanded)
%              Number of equality atoms :  207 (1630 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f900,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f94,f112,f138,f338,f376,f418,f425,f428,f503,f516,f607,f628,f653,f709,f728,f849,f858,f860,f899])).

fof(f899,plain,
    ( spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f897,f872])).

fof(f872,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl8_4
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f705,f137])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl8_7
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f705,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl8_4
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f104,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f104,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl8_4
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f897,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(subsumption_resolution,[],[f888,f879])).

fof(f879,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f751,f137])).

fof(f751,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f44,f109])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( sK1 != k2_relset_1(sK0,sK1,sK2)
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK2,X4) = X3
              & r2_hidden(X4,sK0) )
          | ~ r2_hidden(X3,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f888,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(resolution,[],[f878,f80])).

fof(f80,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f878,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_7 ),
    inference(backward_demodulation,[],[f750,f137])).

fof(f750,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f45,f109])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f860,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f250,f818])).

fof(f818,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(superposition,[],[f784,f783])).

fof(f783,plain,
    ( k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f747,f133])).

fof(f133,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl8_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f747,plain,
    ( k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f98,f109])).

fof(f98,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f784,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f748,f133])).

fof(f748,plain,
    ( k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2)
    | ~ spl8_5 ),
    inference(forward_demodulation,[],[f48,f109])).

fof(f48,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f250,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl8_14
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f858,plain,(
    ~ spl8_15 ),
    inference(avatar_contradiction_clause,[],[f857])).

fof(f857,plain,
    ( $false
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f856,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f856,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_15 ),
    inference(resolution,[],[f254,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f254,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl8_15
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f849,plain,
    ( ~ spl8_6
    | spl8_13
    | spl8_14 ),
    inference(avatar_contradiction_clause,[],[f848])).

fof(f848,plain,
    ( $false
    | ~ spl8_6
    | spl8_13
    | spl8_14 ),
    inference(subsumption_resolution,[],[f847,f49])).

fof(f847,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_6
    | spl8_13
    | spl8_14 ),
    inference(resolution,[],[f844,f56])).

fof(f844,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_6
    | spl8_13
    | spl8_14 ),
    inference(subsumption_resolution,[],[f820,f249])).

fof(f249,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f248])).

fof(f820,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_6
    | spl8_13 ),
    inference(resolution,[],[f792,f204])).

fof(f204,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | spl8_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl8_13
  <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f792,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))
        | r2_hidden(sK4(k1_xboole_0,X0),X0)
        | k2_relat_1(k1_xboole_0) = X0 )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f791,f133])).

fof(f791,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,X0),X0)
        | r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f759,f133])).

fof(f759,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f343,f133])).

fof(f343,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f341,f100])).

fof(f100,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f341,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f43,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK4(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1),X1) )
              & ( ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
                  & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X5)) = X5
                    & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).

fof(f33,plain,(
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
              ( k1_funct_1(X0,X3) != sK4(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK4(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (13460)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f728,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | spl8_32 ),
    inference(avatar_contradiction_clause,[],[f727])).

fof(f727,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | spl8_32 ),
    inference(subsumption_resolution,[],[f726,f683])).

fof(f683,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f360,f109])).

fof(f360,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(superposition,[],[f48,f98])).

fof(f726,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_5
    | spl8_32 ),
    inference(subsumption_resolution,[],[f449,f687])).

fof(f687,plain,
    ( sK4(sK2,k1_xboole_0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0))
    | ~ spl8_5
    | spl8_32 ),
    inference(backward_demodulation,[],[f514,f109])).

fof(f514,plain,
    ( sK4(sK2,sK1) != k1_funct_1(sK2,sK5(sK2,sK1))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl8_32
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f449,plain,
    ( sK4(sK2,k1_xboole_0) = k1_funct_1(sK2,sK5(sK2,k1_xboole_0))
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f379,f49])).

fof(f379,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0))
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f56])).

fof(f93,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1
        | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1)) )
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl8_3
  <=> ! [X1] :
        ( sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1))
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK4(sK2,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f709,plain,
    ( ~ spl8_7
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl8_7
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f707,f49])).

fof(f707,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_7
    | ~ spl8_23 ),
    inference(forward_demodulation,[],[f517,f137])).

fof(f517,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl8_23 ),
    inference(resolution,[],[f412,f56])).

fof(f412,plain,
    ( r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl8_23
  <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f653,plain,
    ( spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f652,f107,f103])).

fof(f652,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f347,f44])).

fof(f347,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f628,plain,
    ( ~ spl8_24
    | ~ spl8_25 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f626,f360])).

fof(f626,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl8_24
    | ~ spl8_25 ),
    inference(subsumption_resolution,[],[f625,f609])).

fof(f609,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_24 ),
    inference(resolution,[],[f417,f358])).

fof(f358,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f346,f59])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f346,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(subsumption_resolution,[],[f345,f100])).

fof(f345,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f97,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f45,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f417,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f415])).

fof(f415,plain,
    ( spl8_24
  <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f625,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_25 ),
    inference(equality_resolution,[],[f424])).

fof(f424,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl8_25
  <=> ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f607,plain,
    ( ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f606])).

fof(f606,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f605,f521])).

fof(f521,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f518,f375])).

fof(f375,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl8_20
  <=> r2_hidden(sK5(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f518,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl8_4
    | ~ spl8_32 ),
    inference(superposition,[],[f402,f515])).

fof(f515,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f513])).

fof(f402,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(resolution,[],[f358,f356])).

fof(f356,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f355,f100])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f354,f43])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4 ),
    inference(superposition,[],[f73,f339])).

fof(f339,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f99,f105])).

fof(f105,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f99,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f73,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f605,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f604,f360])).

fof(f604,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(equality_resolution,[],[f528])).

fof(f528,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_4
    | ~ spl8_20
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f527,f375])).

fof(f527,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK2,sK1),sK0)
        | sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_4
    | ~ spl8_32 ),
    inference(forward_demodulation,[],[f526,f339])).

fof(f526,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f525,f100])).

fof(f525,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f520,f43])).

fof(f520,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_32 ),
    inference(superposition,[],[f55,f515])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK4(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f516,plain,
    ( spl8_19
    | spl8_32
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f511,f92,f513,f369])).

fof(f369,plain,
    ( spl8_19
  <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f511,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f383,f360])).

fof(f383,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_3 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f503,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | ~ spl8_20
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f502])).

fof(f502,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f501,f375])).

fof(f501,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_23 ),
    inference(subsumption_resolution,[],[f498,f426])).

fof(f426,plain,
    ( ~ r2_hidden(sK4(sK2,sK1),sK1)
    | spl8_23 ),
    inference(resolution,[],[f413,f46])).

fof(f46,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f413,plain,
    ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f411])).

fof(f498,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ r2_hidden(sK5(sK2,sK1),sK0)
    | ~ spl8_3
    | ~ spl8_4
    | spl8_23 ),
    inference(superposition,[],[f402,f437])).

fof(f437,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ spl8_3
    | spl8_23 ),
    inference(subsumption_resolution,[],[f435,f360])).

fof(f435,plain,
    ( sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))
    | ~ spl8_3
    | spl8_23 ),
    inference(resolution,[],[f426,f93])).

fof(f428,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | spl8_20
    | spl8_23 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20
    | spl8_23 ),
    inference(subsumption_resolution,[],[f426,f378])).

fof(f378,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(subsumption_resolution,[],[f377,f360])).

fof(f377,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_2
    | ~ spl8_4
    | spl8_20 ),
    inference(resolution,[],[f374,f340])).

fof(f340,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),sK0)
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f89,f339])).

fof(f89,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl8_2
  <=> ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f374,plain,
    ( ~ r2_hidden(sK5(sK2,sK1),sK0)
    | spl8_20 ),
    inference(avatar_component_clause,[],[f373])).

fof(f425,plain,
    ( spl8_25
    | ~ spl8_23
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f421,f369,f103,f411,f423])).

fof(f421,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
        | sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f420,f339])).

fof(f420,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f419,f100])).

fof(f419,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f409,f43])).

fof(f409,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) != sK4(sK2,sK1)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_19 ),
    inference(superposition,[],[f55,f371])).

fof(f371,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f369])).

fof(f418,plain,
    ( ~ spl8_23
    | spl8_24
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f408,f369,f103,f415,f411])).

fof(f408,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ r2_hidden(sK3(sK4(sK2,sK1)),sK0)
    | ~ spl8_4
    | ~ spl8_19 ),
    inference(superposition,[],[f356,f371])).

% (13453)Refutation not found, incomplete strategy% (13453)------------------------------
% (13453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f376,plain,
    ( spl8_19
    | spl8_20
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f367,f103,f88,f373,f369])).

fof(f367,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f366,f360])).

fof(f366,plain,
    ( r2_hidden(sK5(sK2,sK1),sK0)
    | sK1 = k2_relat_1(sK2)
    | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f340,f47])).

fof(f338,plain,
    ( ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_14
    | spl8_15 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_14
    | spl8_15 ),
    inference(subsumption_resolution,[],[f335,f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f252])).

fof(f335,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13
    | spl8_14
    | spl8_15 ),
    inference(backward_demodulation,[],[f317,f332])).

fof(f332,plain,
    ( sK4(k1_xboole_0,k1_xboole_0) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0))
    | ~ spl8_3
    | ~ spl8_6
    | spl8_14
    | spl8_15 ),
    inference(subsumption_resolution,[],[f325,f249])).

fof(f325,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | sK4(k1_xboole_0,k1_xboole_0) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0))
    | ~ spl8_3
    | ~ spl8_6
    | spl8_15 ),
    inference(resolution,[],[f154,f253])).

fof(f154,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(k1_xboole_0,X1),X1)
        | k2_relat_1(k1_xboole_0) = X1
        | sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1)) )
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f153,f133])).

fof(f153,plain,
    ( ! [X1] :
        ( k2_relat_1(k1_xboole_0) = X1
        | sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1))
        | r2_hidden(sK4(sK2,X1),X1) )
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f141,f133])).

fof(f141,plain,
    ( ! [X1] :
        ( sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1))
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK4(sK2,X1),X1) )
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f93,f133])).

fof(f317,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(resolution,[],[f305,f280])).

fof(f280,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | r2_hidden(X0,k1_xboole_0) )
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f229,f109])).

fof(f229,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_6 ),
    inference(resolution,[],[f224,f59])).

fof(f224,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f223,f142])).

fof(f142,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f100,f133])).

fof(f223,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK1)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(resolution,[],[f209,f57])).

fof(f209,plain,
    ( v5_relat_1(k1_xboole_0,sK1)
    | ~ spl8_6 ),
    inference(forward_demodulation,[],[f97,f133])).

fof(f305,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f304,f142])).

fof(f304,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f302,f139])).

fof(f139,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f43,f133])).

fof(f302,plain,
    ( r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl8_13 ),
    inference(resolution,[],[f205,f73])).

fof(f205,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f203])).

fof(f138,plain,
    ( spl8_6
    | spl8_7
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f129,f107,f135,f131])).

fof(f129,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f122,f113])).

fof(f113,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f44,f109])).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,sK0,k1_xboole_0)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl8_5 ),
    inference(resolution,[],[f114,f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f45,f109])).

fof(f112,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f100,f86])).

fof(f86,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl8_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f94,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_split_clause,[],[f82,f92,f84])).

fof(f82,plain,(
    ! [X1] :
      ( sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1))
      | r2_hidden(sK4(sK2,X1),X1)
      | k2_relat_1(sK2) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f81,f88,f84])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f43,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (13439)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (13458)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (13450)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (13441)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (13442)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (13444)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (13448)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (13437)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (13449)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (13454)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (13462)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (13436)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (13464)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.54  % (13465)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (13456)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (13451)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (13445)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (13458)Refutation not found, incomplete strategy% (13458)------------------------------
% 1.41/0.55  % (13458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13458)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13458)Memory used [KB]: 10874
% 1.41/0.55  % (13458)Time elapsed: 0.090 s
% 1.41/0.55  % (13458)------------------------------
% 1.41/0.55  % (13458)------------------------------
% 1.41/0.55  % (13457)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  % (13440)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.55  % (13455)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.55  % (13443)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.55  % (13459)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (13446)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (13446)Refutation not found, incomplete strategy% (13446)------------------------------
% 1.41/0.55  % (13446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13446)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13446)Memory used [KB]: 10746
% 1.41/0.55  % (13446)Time elapsed: 0.135 s
% 1.41/0.55  % (13446)------------------------------
% 1.41/0.55  % (13446)------------------------------
% 1.41/0.55  % (13447)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.53/0.55  % (13452)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.53/0.56  % (13438)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.53/0.56  % (13453)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.53/0.56  % (13463)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.56  % (13444)Refutation found. Thanks to Tanya!
% 1.53/0.56  % SZS status Theorem for theBenchmark
% 1.53/0.56  % (13461)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.53/0.58  % (13447)Refutation not found, incomplete strategy% (13447)------------------------------
% 1.53/0.58  % (13447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (13447)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (13447)Memory used [KB]: 10746
% 1.53/0.58  % (13447)Time elapsed: 0.151 s
% 1.53/0.58  % (13447)------------------------------
% 1.53/0.58  % (13447)------------------------------
% 1.53/0.58  % SZS output start Proof for theBenchmark
% 1.53/0.58  fof(f900,plain,(
% 1.53/0.58    $false),
% 1.53/0.58    inference(avatar_sat_refutation,[],[f90,f94,f112,f138,f338,f376,f418,f425,f428,f503,f516,f607,f628,f653,f709,f728,f849,f858,f860,f899])).
% 1.53/0.58  fof(f899,plain,(
% 1.53/0.58    spl8_4 | ~spl8_5 | ~spl8_7),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f898])).
% 1.53/0.58  fof(f898,plain,(
% 1.53/0.58    $false | (spl8_4 | ~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(subsumption_resolution,[],[f897,f872])).
% 1.53/0.58  fof(f872,plain,(
% 1.53/0.58    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl8_4 | ~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(backward_demodulation,[],[f705,f137])).
% 1.53/0.58  fof(f137,plain,(
% 1.53/0.58    k1_xboole_0 = sK0 | ~spl8_7),
% 1.53/0.58    inference(avatar_component_clause,[],[f135])).
% 1.53/0.58  fof(f135,plain,(
% 1.53/0.58    spl8_7 <=> k1_xboole_0 = sK0),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.53/0.58  fof(f705,plain,(
% 1.53/0.58    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl8_4 | ~spl8_5)),
% 1.53/0.58    inference(forward_demodulation,[],[f104,f109])).
% 1.53/0.58  fof(f109,plain,(
% 1.53/0.58    k1_xboole_0 = sK1 | ~spl8_5),
% 1.53/0.58    inference(avatar_component_clause,[],[f107])).
% 1.53/0.58  fof(f107,plain,(
% 1.53/0.58    spl8_5 <=> k1_xboole_0 = sK1),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.53/0.58  fof(f104,plain,(
% 1.53/0.58    sK0 != k1_relset_1(sK0,sK1,sK2) | spl8_4),
% 1.53/0.58    inference(avatar_component_clause,[],[f103])).
% 1.53/0.58  fof(f103,plain,(
% 1.53/0.58    spl8_4 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.53/0.58  fof(f897,plain,(
% 1.53/0.58    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(subsumption_resolution,[],[f888,f879])).
% 1.53/0.58  fof(f879,plain,(
% 1.53/0.58    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(backward_demodulation,[],[f751,f137])).
% 1.53/0.58  fof(f751,plain,(
% 1.53/0.58    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_5),
% 1.53/0.58    inference(forward_demodulation,[],[f44,f109])).
% 1.53/0.58  fof(f44,plain,(
% 1.53/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f30,plain,(
% 1.53/0.58    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f29,f28])).
% 1.53/0.58  fof(f28,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f29,plain,(
% 1.53/0.58    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f16,plain,(
% 1.53/0.58    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.53/0.58    inference(flattening,[],[f15])).
% 1.53/0.58  fof(f15,plain,(
% 1.53/0.58    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.53/0.58    inference(ennf_transformation,[],[f12])).
% 1.53/0.58  fof(f12,negated_conjecture,(
% 1.53/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.53/0.58    inference(negated_conjecture,[],[f11])).
% 1.53/0.58  fof(f11,conjecture,(
% 1.53/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 1.53/0.58  fof(f888,plain,(
% 1.53/0.58    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(resolution,[],[f878,f80])).
% 1.53/0.58  fof(f80,plain,(
% 1.53/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.53/0.58    inference(equality_resolution,[],[f67])).
% 1.53/0.58  fof(f67,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f42,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(nnf_transformation,[],[f27])).
% 1.53/0.58  fof(f27,plain,(
% 1.53/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(flattening,[],[f26])).
% 1.53/0.58  fof(f26,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f10])).
% 1.53/0.58  fof(f10,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.53/0.58  fof(f878,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl8_5 | ~spl8_7)),
% 1.53/0.58    inference(backward_demodulation,[],[f750,f137])).
% 1.53/0.58  fof(f750,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_5),
% 1.53/0.58    inference(forward_demodulation,[],[f45,f109])).
% 1.53/0.58  fof(f45,plain,(
% 1.53/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f860,plain,(
% 1.53/0.58    ~spl8_5 | ~spl8_6 | ~spl8_14),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f859])).
% 1.53/0.58  fof(f859,plain,(
% 1.53/0.58    $false | (~spl8_5 | ~spl8_6 | ~spl8_14)),
% 1.53/0.58    inference(subsumption_resolution,[],[f250,f818])).
% 1.53/0.58  fof(f818,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relat_1(k1_xboole_0) | (~spl8_5 | ~spl8_6)),
% 1.53/0.58    inference(superposition,[],[f784,f783])).
% 1.53/0.58  fof(f783,plain,(
% 1.53/0.58    k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl8_5 | ~spl8_6)),
% 1.53/0.58    inference(backward_demodulation,[],[f747,f133])).
% 1.53/0.58  fof(f133,plain,(
% 1.53/0.58    k1_xboole_0 = sK2 | ~spl8_6),
% 1.53/0.58    inference(avatar_component_clause,[],[f131])).
% 1.53/0.58  fof(f131,plain,(
% 1.53/0.58    spl8_6 <=> k1_xboole_0 = sK2),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.53/0.58  fof(f747,plain,(
% 1.53/0.58    k2_relat_1(sK2) = k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl8_5),
% 1.53/0.58    inference(forward_demodulation,[],[f98,f109])).
% 1.53/0.58  fof(f98,plain,(
% 1.53/0.58    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.53/0.58    inference(resolution,[],[f45,f64])).
% 1.53/0.58  fof(f64,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f24])).
% 1.53/0.58  fof(f24,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f9])).
% 1.53/0.58  fof(f9,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.53/0.58  fof(f784,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,k1_xboole_0) | (~spl8_5 | ~spl8_6)),
% 1.53/0.58    inference(backward_demodulation,[],[f748,f133])).
% 1.53/0.58  fof(f748,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relset_1(sK0,k1_xboole_0,sK2) | ~spl8_5),
% 1.53/0.58    inference(forward_demodulation,[],[f48,f109])).
% 1.53/0.58  fof(f48,plain,(
% 1.53/0.58    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f250,plain,(
% 1.53/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_14),
% 1.53/0.58    inference(avatar_component_clause,[],[f248])).
% 1.53/0.58  fof(f248,plain,(
% 1.53/0.58    spl8_14 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.53/0.58  fof(f858,plain,(
% 1.53/0.58    ~spl8_15),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f857])).
% 1.53/0.58  fof(f857,plain,(
% 1.53/0.58    $false | ~spl8_15),
% 1.53/0.58    inference(subsumption_resolution,[],[f856,f49])).
% 1.53/0.58  fof(f49,plain,(
% 1.53/0.58    v1_xboole_0(k1_xboole_0)),
% 1.53/0.58    inference(cnf_transformation,[],[f3])).
% 1.53/0.58  fof(f3,axiom,(
% 1.53/0.58    v1_xboole_0(k1_xboole_0)),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.53/0.58  fof(f856,plain,(
% 1.53/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl8_15),
% 1.53/0.58    inference(resolution,[],[f254,f56])).
% 1.53/0.58  fof(f56,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f19])).
% 1.53/0.58  fof(f19,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.53/0.58    inference(ennf_transformation,[],[f13])).
% 1.53/0.58  fof(f13,plain,(
% 1.53/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.53/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 1.53/0.58  fof(f1,axiom,(
% 1.53/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.53/0.58  fof(f254,plain,(
% 1.53/0.58    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl8_15),
% 1.53/0.58    inference(avatar_component_clause,[],[f252])).
% 1.53/0.58  fof(f252,plain,(
% 1.53/0.58    spl8_15 <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.53/0.58  fof(f849,plain,(
% 1.53/0.58    ~spl8_6 | spl8_13 | spl8_14),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f848])).
% 1.53/0.58  fof(f848,plain,(
% 1.53/0.58    $false | (~spl8_6 | spl8_13 | spl8_14)),
% 1.53/0.58    inference(subsumption_resolution,[],[f847,f49])).
% 1.53/0.58  fof(f847,plain,(
% 1.53/0.58    ~v1_xboole_0(k1_xboole_0) | (~spl8_6 | spl8_13 | spl8_14)),
% 1.53/0.58    inference(resolution,[],[f844,f56])).
% 1.53/0.58  fof(f844,plain,(
% 1.53/0.58    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl8_6 | spl8_13 | spl8_14)),
% 1.53/0.58    inference(subsumption_resolution,[],[f820,f249])).
% 1.53/0.58  fof(f249,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl8_14),
% 1.53/0.58    inference(avatar_component_clause,[],[f248])).
% 1.53/0.58  fof(f820,plain,(
% 1.53/0.58    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl8_6 | spl8_13)),
% 1.53/0.58    inference(resolution,[],[f792,f204])).
% 1.53/0.58  fof(f204,plain,(
% 1.53/0.58    ~r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | spl8_13),
% 1.53/0.58    inference(avatar_component_clause,[],[f203])).
% 1.53/0.58  fof(f203,plain,(
% 1.53/0.58    spl8_13 <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.53/0.58  fof(f792,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) | r2_hidden(sK4(k1_xboole_0,X0),X0) | k2_relat_1(k1_xboole_0) = X0) ) | ~spl8_6),
% 1.53/0.58    inference(forward_demodulation,[],[f791,f133])).
% 1.53/0.58  fof(f791,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK4(k1_xboole_0,X0),X0) | r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) | k2_relat_1(sK2) = X0) ) | ~spl8_6),
% 1.53/0.58    inference(forward_demodulation,[],[f759,f133])).
% 1.53/0.58  fof(f759,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl8_6),
% 1.53/0.58    inference(backward_demodulation,[],[f343,f133])).
% 1.53/0.58  fof(f343,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) )),
% 1.53/0.58    inference(subsumption_resolution,[],[f341,f100])).
% 1.53/0.58  fof(f100,plain,(
% 1.53/0.58    v1_relat_1(sK2)),
% 1.53/0.58    inference(resolution,[],[f45,f62])).
% 1.53/0.58  fof(f62,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f22])).
% 1.53/0.58  fof(f22,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f6])).
% 1.53/0.58  fof(f6,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.53/0.58  fof(f341,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) )),
% 1.53/0.58    inference(resolution,[],[f43,f53])).
% 1.53/0.58  fof(f53,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f36])).
% 1.53/0.58  fof(f36,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f32,f35,f34,f33])).
% 1.53/0.58  fof(f33,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  % (13460)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.53/0.58  fof(f34,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f35,plain,(
% 1.53/0.58    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f32,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(rectify,[],[f31])).
% 1.53/0.58  fof(f31,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(nnf_transformation,[],[f18])).
% 1.53/0.58  fof(f18,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.53/0.58    inference(flattening,[],[f17])).
% 1.53/0.58  fof(f17,plain,(
% 1.53/0.58    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f5])).
% 1.53/0.58  fof(f5,axiom,(
% 1.53/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 1.53/0.58  fof(f43,plain,(
% 1.53/0.58    v1_funct_1(sK2)),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f728,plain,(
% 1.53/0.58    ~spl8_3 | ~spl8_5 | spl8_32),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f727])).
% 1.53/0.58  fof(f727,plain,(
% 1.53/0.58    $false | (~spl8_3 | ~spl8_5 | spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f726,f683])).
% 1.53/0.58  fof(f683,plain,(
% 1.53/0.58    k1_xboole_0 != k2_relat_1(sK2) | ~spl8_5),
% 1.53/0.58    inference(backward_demodulation,[],[f360,f109])).
% 1.53/0.58  fof(f360,plain,(
% 1.53/0.58    sK1 != k2_relat_1(sK2)),
% 1.53/0.58    inference(superposition,[],[f48,f98])).
% 1.53/0.58  fof(f726,plain,(
% 1.53/0.58    k1_xboole_0 = k2_relat_1(sK2) | (~spl8_3 | ~spl8_5 | spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f449,f687])).
% 1.53/0.58  fof(f687,plain,(
% 1.53/0.58    sK4(sK2,k1_xboole_0) != k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) | (~spl8_5 | spl8_32)),
% 1.53/0.58    inference(backward_demodulation,[],[f514,f109])).
% 1.53/0.58  fof(f514,plain,(
% 1.53/0.58    sK4(sK2,sK1) != k1_funct_1(sK2,sK5(sK2,sK1)) | spl8_32),
% 1.53/0.58    inference(avatar_component_clause,[],[f513])).
% 1.53/0.58  fof(f513,plain,(
% 1.53/0.58    spl8_32 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.53/0.58  fof(f449,plain,(
% 1.53/0.58    sK4(sK2,k1_xboole_0) = k1_funct_1(sK2,sK5(sK2,k1_xboole_0)) | k1_xboole_0 = k2_relat_1(sK2) | ~spl8_3),
% 1.53/0.58    inference(resolution,[],[f379,f49])).
% 1.53/0.58  fof(f379,plain,(
% 1.53/0.58    ( ! [X0] : (~v1_xboole_0(X0) | sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0)) | k2_relat_1(sK2) = X0) ) | ~spl8_3),
% 1.53/0.58    inference(resolution,[],[f93,f56])).
% 1.53/0.58  fof(f93,plain,(
% 1.53/0.58    ( ! [X1] : (r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1 | sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1))) ) | ~spl8_3),
% 1.53/0.58    inference(avatar_component_clause,[],[f92])).
% 1.53/0.58  fof(f92,plain,(
% 1.53/0.58    spl8_3 <=> ! [X1] : (sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1)) | k2_relat_1(sK2) = X1 | r2_hidden(sK4(sK2,X1),X1))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.53/0.58  fof(f709,plain,(
% 1.53/0.58    ~spl8_7 | ~spl8_23),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f708])).
% 1.53/0.58  fof(f708,plain,(
% 1.53/0.58    $false | (~spl8_7 | ~spl8_23)),
% 1.53/0.58    inference(subsumption_resolution,[],[f707,f49])).
% 1.53/0.58  fof(f707,plain,(
% 1.53/0.58    ~v1_xboole_0(k1_xboole_0) | (~spl8_7 | ~spl8_23)),
% 1.53/0.58    inference(forward_demodulation,[],[f517,f137])).
% 1.53/0.58  fof(f517,plain,(
% 1.53/0.58    ~v1_xboole_0(sK0) | ~spl8_23),
% 1.53/0.58    inference(resolution,[],[f412,f56])).
% 1.53/0.58  fof(f412,plain,(
% 1.53/0.58    r2_hidden(sK3(sK4(sK2,sK1)),sK0) | ~spl8_23),
% 1.53/0.58    inference(avatar_component_clause,[],[f411])).
% 1.53/0.58  fof(f411,plain,(
% 1.53/0.58    spl8_23 <=> r2_hidden(sK3(sK4(sK2,sK1)),sK0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.53/0.58  fof(f653,plain,(
% 1.53/0.58    spl8_4 | spl8_5),
% 1.53/0.58    inference(avatar_split_clause,[],[f652,f107,f103])).
% 1.53/0.58  fof(f652,plain,(
% 1.53/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(subsumption_resolution,[],[f347,f44])).
% 1.53/0.58  fof(f347,plain,(
% 1.53/0.58    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(resolution,[],[f45,f66])).
% 1.53/0.58  fof(f66,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.53/0.58    inference(cnf_transformation,[],[f42])).
% 1.53/0.58  fof(f628,plain,(
% 1.53/0.58    ~spl8_24 | ~spl8_25),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f627])).
% 1.53/0.58  fof(f627,plain,(
% 1.53/0.58    $false | (~spl8_24 | ~spl8_25)),
% 1.53/0.58    inference(subsumption_resolution,[],[f626,f360])).
% 1.53/0.58  fof(f626,plain,(
% 1.53/0.58    sK1 = k2_relat_1(sK2) | (~spl8_24 | ~spl8_25)),
% 1.53/0.58    inference(subsumption_resolution,[],[f625,f609])).
% 1.53/0.58  fof(f609,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | ~spl8_24),
% 1.53/0.58    inference(resolution,[],[f417,f358])).
% 1.53/0.58  fof(f358,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | r2_hidden(X0,sK1)) )),
% 1.53/0.58    inference(resolution,[],[f346,f59])).
% 1.53/0.58  fof(f59,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f41])).
% 1.53/0.58  fof(f41,plain,(
% 1.53/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).
% 1.53/0.58  fof(f40,plain,(
% 1.53/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.53/0.58    introduced(choice_axiom,[])).
% 1.53/0.58  fof(f39,plain,(
% 1.53/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.58    inference(rectify,[],[f38])).
% 1.53/0.58  fof(f38,plain,(
% 1.53/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.53/0.58    inference(nnf_transformation,[],[f21])).
% 1.53/0.58  fof(f21,plain,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.53/0.58    inference(ennf_transformation,[],[f2])).
% 1.53/0.58  fof(f2,axiom,(
% 1.53/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.58  fof(f346,plain,(
% 1.53/0.58    r1_tarski(k2_relat_1(sK2),sK1)),
% 1.53/0.58    inference(subsumption_resolution,[],[f345,f100])).
% 1.53/0.58  fof(f345,plain,(
% 1.53/0.58    r1_tarski(k2_relat_1(sK2),sK1) | ~v1_relat_1(sK2)),
% 1.53/0.58    inference(resolution,[],[f97,f57])).
% 1.53/0.58  fof(f57,plain,(
% 1.53/0.58    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f37])).
% 1.53/0.58  fof(f37,plain,(
% 1.53/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(nnf_transformation,[],[f20])).
% 1.53/0.58  fof(f20,plain,(
% 1.53/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.53/0.58    inference(ennf_transformation,[],[f4])).
% 1.53/0.58  fof(f4,axiom,(
% 1.53/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.53/0.58  fof(f97,plain,(
% 1.53/0.58    v5_relat_1(sK2,sK1)),
% 1.53/0.58    inference(resolution,[],[f45,f65])).
% 1.53/0.58  fof(f65,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f25])).
% 1.53/0.58  fof(f25,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f14])).
% 1.53/0.58  fof(f14,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.53/0.58    inference(pure_predicate_removal,[],[f7])).
% 1.53/0.58  fof(f7,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.53/0.58  fof(f417,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~spl8_24),
% 1.53/0.58    inference(avatar_component_clause,[],[f415])).
% 1.53/0.58  fof(f415,plain,(
% 1.53/0.58    spl8_24 <=> r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.53/0.58  fof(f625,plain,(
% 1.53/0.58    ~r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | ~spl8_25),
% 1.53/0.58    inference(equality_resolution,[],[f424])).
% 1.53/0.58  fof(f424,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl8_25),
% 1.53/0.58    inference(avatar_component_clause,[],[f423])).
% 1.53/0.58  fof(f423,plain,(
% 1.53/0.58    spl8_25 <=> ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.53/0.58  fof(f607,plain,(
% 1.53/0.58    ~spl8_4 | ~spl8_20 | ~spl8_32),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f606])).
% 1.53/0.58  fof(f606,plain,(
% 1.53/0.58    $false | (~spl8_4 | ~spl8_20 | ~spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f605,f521])).
% 1.53/0.58  fof(f521,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_4 | ~spl8_20 | ~spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f518,f375])).
% 1.53/0.58  fof(f375,plain,(
% 1.53/0.58    r2_hidden(sK5(sK2,sK1),sK0) | ~spl8_20),
% 1.53/0.58    inference(avatar_component_clause,[],[f373])).
% 1.53/0.58  fof(f373,plain,(
% 1.53/0.58    spl8_20 <=> r2_hidden(sK5(sK2,sK1),sK0)),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.53/0.58  fof(f518,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl8_4 | ~spl8_32)),
% 1.53/0.58    inference(superposition,[],[f402,f515])).
% 1.53/0.58  fof(f515,plain,(
% 1.53/0.58    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | ~spl8_32),
% 1.53/0.58    inference(avatar_component_clause,[],[f513])).
% 1.53/0.58  fof(f402,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),sK1) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 1.53/0.58    inference(resolution,[],[f358,f356])).
% 1.53/0.58  fof(f356,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~r2_hidden(X0,sK0)) ) | ~spl8_4),
% 1.53/0.58    inference(subsumption_resolution,[],[f355,f100])).
% 1.53/0.58  fof(f355,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl8_4),
% 1.53/0.58    inference(subsumption_resolution,[],[f354,f43])).
% 1.53/0.58  fof(f354,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_4),
% 1.53/0.58    inference(superposition,[],[f73,f339])).
% 1.53/0.58  fof(f339,plain,(
% 1.53/0.58    sK0 = k1_relat_1(sK2) | ~spl8_4),
% 1.53/0.58    inference(backward_demodulation,[],[f99,f105])).
% 1.53/0.58  fof(f105,plain,(
% 1.53/0.58    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_4),
% 1.53/0.58    inference(avatar_component_clause,[],[f103])).
% 1.53/0.58  fof(f99,plain,(
% 1.53/0.58    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.53/0.58    inference(resolution,[],[f45,f63])).
% 1.53/0.58  fof(f63,plain,(
% 1.53/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f23])).
% 1.53/0.58  fof(f23,plain,(
% 1.53/0.58    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.53/0.58    inference(ennf_transformation,[],[f8])).
% 1.53/0.58  fof(f8,axiom,(
% 1.53/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.53/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.53/0.58  fof(f73,plain,(
% 1.53/0.58    ( ! [X6,X0] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(equality_resolution,[],[f72])).
% 1.53/0.58  fof(f72,plain,(
% 1.53/0.58    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(equality_resolution,[],[f52])).
% 1.53/0.58  fof(f52,plain,(
% 1.53/0.58    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f36])).
% 1.53/0.58  fof(f605,plain,(
% 1.53/0.58    ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_4 | ~spl8_20 | ~spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f604,f360])).
% 1.53/0.58  fof(f604,plain,(
% 1.53/0.58    sK1 = k2_relat_1(sK2) | ~r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_4 | ~spl8_20 | ~spl8_32)),
% 1.53/0.58    inference(equality_resolution,[],[f528])).
% 1.53/0.58  fof(f528,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl8_4 | ~spl8_20 | ~spl8_32)),
% 1.53/0.58    inference(subsumption_resolution,[],[f527,f375])).
% 1.53/0.58  fof(f527,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(sK5(sK2,sK1),sK0) | sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl8_4 | ~spl8_32)),
% 1.53/0.58    inference(forward_demodulation,[],[f526,f339])).
% 1.53/0.58  fof(f526,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_32),
% 1.53/0.58    inference(subsumption_resolution,[],[f525,f100])).
% 1.53/0.58  fof(f525,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_relat_1(sK2)) ) | ~spl8_32),
% 1.53/0.58    inference(subsumption_resolution,[],[f520,f43])).
% 1.53/0.58  fof(f520,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK5(sK2,sK1),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_32),
% 1.53/0.58    inference(superposition,[],[f55,f515])).
% 1.53/0.58  fof(f55,plain,(
% 1.53/0.58    ( ! [X0,X3,X1] : (k1_funct_1(X0,X3) != sK4(X0,X1) | k2_relat_1(X0) = X1 | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f36])).
% 1.53/0.58  fof(f516,plain,(
% 1.53/0.58    spl8_19 | spl8_32 | ~spl8_3),
% 1.53/0.58    inference(avatar_split_clause,[],[f511,f92,f513,f369])).
% 1.53/0.58  fof(f369,plain,(
% 1.53/0.58    spl8_19 <=> sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.53/0.58  fof(f511,plain,(
% 1.53/0.58    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_3),
% 1.53/0.58    inference(subsumption_resolution,[],[f383,f360])).
% 1.53/0.58  fof(f383,plain,(
% 1.53/0.58    sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_3),
% 1.53/0.58    inference(resolution,[],[f93,f47])).
% 1.53/0.58  fof(f47,plain,(
% 1.53/0.58    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f503,plain,(
% 1.53/0.58    ~spl8_3 | ~spl8_4 | ~spl8_20 | spl8_23),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f502])).
% 1.53/0.58  fof(f502,plain,(
% 1.53/0.58    $false | (~spl8_3 | ~spl8_4 | ~spl8_20 | spl8_23)),
% 1.53/0.58    inference(subsumption_resolution,[],[f501,f375])).
% 1.53/0.58  fof(f501,plain,(
% 1.53/0.58    ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl8_3 | ~spl8_4 | spl8_23)),
% 1.53/0.58    inference(subsumption_resolution,[],[f498,f426])).
% 1.53/0.58  fof(f426,plain,(
% 1.53/0.58    ~r2_hidden(sK4(sK2,sK1),sK1) | spl8_23),
% 1.53/0.58    inference(resolution,[],[f413,f46])).
% 1.53/0.58  fof(f46,plain,(
% 1.53/0.58    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 1.53/0.58    inference(cnf_transformation,[],[f30])).
% 1.53/0.58  fof(f413,plain,(
% 1.53/0.58    ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | spl8_23),
% 1.53/0.58    inference(avatar_component_clause,[],[f411])).
% 1.53/0.58  fof(f498,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | ~r2_hidden(sK5(sK2,sK1),sK0) | (~spl8_3 | ~spl8_4 | spl8_23)),
% 1.53/0.58    inference(superposition,[],[f402,f437])).
% 1.53/0.58  fof(f437,plain,(
% 1.53/0.58    sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | (~spl8_3 | spl8_23)),
% 1.53/0.58    inference(subsumption_resolution,[],[f435,f360])).
% 1.53/0.58  fof(f435,plain,(
% 1.53/0.58    sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK5(sK2,sK1)) | (~spl8_3 | spl8_23)),
% 1.53/0.58    inference(resolution,[],[f426,f93])).
% 1.53/0.58  fof(f428,plain,(
% 1.53/0.58    ~spl8_2 | ~spl8_4 | spl8_20 | spl8_23),
% 1.53/0.58    inference(avatar_contradiction_clause,[],[f427])).
% 1.53/0.58  fof(f427,plain,(
% 1.53/0.58    $false | (~spl8_2 | ~spl8_4 | spl8_20 | spl8_23)),
% 1.53/0.58    inference(subsumption_resolution,[],[f426,f378])).
% 1.53/0.58  fof(f378,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_2 | ~spl8_4 | spl8_20)),
% 1.53/0.58    inference(subsumption_resolution,[],[f377,f360])).
% 1.53/0.58  fof(f377,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl8_2 | ~spl8_4 | spl8_20)),
% 1.53/0.58    inference(resolution,[],[f374,f340])).
% 1.53/0.58  fof(f340,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),sK0) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl8_2 | ~spl8_4)),
% 1.53/0.58    inference(backward_demodulation,[],[f89,f339])).
% 1.53/0.58  fof(f89,plain,(
% 1.53/0.58    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_2),
% 1.53/0.58    inference(avatar_component_clause,[],[f88])).
% 1.53/0.58  fof(f88,plain,(
% 1.53/0.58    spl8_2 <=> ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0))),
% 1.53/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.53/0.58  fof(f374,plain,(
% 1.53/0.58    ~r2_hidden(sK5(sK2,sK1),sK0) | spl8_20),
% 1.53/0.58    inference(avatar_component_clause,[],[f373])).
% 1.53/0.58  fof(f425,plain,(
% 1.53/0.58    spl8_25 | ~spl8_23 | ~spl8_4 | ~spl8_19),
% 1.53/0.58    inference(avatar_split_clause,[],[f421,f369,f103,f411,f423])).
% 1.53/0.58  fof(f421,plain,(
% 1.53/0.58    ( ! [X0] : (~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK4(sK2,X0),X0)) ) | (~spl8_4 | ~spl8_19)),
% 1.53/0.58    inference(forward_demodulation,[],[f420,f339])).
% 1.53/0.58  fof(f420,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_19),
% 1.53/0.58    inference(subsumption_resolution,[],[f419,f100])).
% 1.53/0.58  fof(f419,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_relat_1(sK2)) ) | ~spl8_19),
% 1.53/0.58    inference(subsumption_resolution,[],[f409,f43])).
% 1.53/0.58  fof(f409,plain,(
% 1.53/0.58    ( ! [X0] : (sK4(sK2,X0) != sK4(sK2,sK1) | k2_relat_1(sK2) = X0 | ~r2_hidden(sK3(sK4(sK2,sK1)),k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X0),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_19),
% 1.53/0.58    inference(superposition,[],[f55,f371])).
% 1.53/0.58  fof(f371,plain,(
% 1.53/0.58    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | ~spl8_19),
% 1.53/0.58    inference(avatar_component_clause,[],[f369])).
% 1.53/0.58  fof(f418,plain,(
% 1.53/0.58    ~spl8_23 | spl8_24 | ~spl8_4 | ~spl8_19),
% 1.53/0.58    inference(avatar_split_clause,[],[f408,f369,f103,f415,f411])).
% 1.53/0.58  fof(f408,plain,(
% 1.53/0.58    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | ~r2_hidden(sK3(sK4(sK2,sK1)),sK0) | (~spl8_4 | ~spl8_19)),
% 1.53/0.58    inference(superposition,[],[f356,f371])).
% 1.53/0.58  % (13453)Refutation not found, incomplete strategy% (13453)------------------------------
% 1.53/0.58  % (13453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  fof(f376,plain,(
% 1.53/0.59    spl8_19 | spl8_20 | ~spl8_2 | ~spl8_4),
% 1.53/0.59    inference(avatar_split_clause,[],[f367,f103,f88,f373,f369])).
% 1.53/0.59  fof(f367,plain,(
% 1.53/0.59    r2_hidden(sK5(sK2,sK1),sK0) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_2 | ~spl8_4)),
% 1.53/0.59    inference(subsumption_resolution,[],[f366,f360])).
% 1.53/0.59  fof(f366,plain,(
% 1.53/0.59    r2_hidden(sK5(sK2,sK1),sK0) | sK1 = k2_relat_1(sK2) | sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_2 | ~spl8_4)),
% 1.53/0.59    inference(resolution,[],[f340,f47])).
% 1.53/0.59  fof(f338,plain,(
% 1.53/0.59    ~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_14 | spl8_15),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f337])).
% 1.53/0.59  fof(f337,plain,(
% 1.53/0.59    $false | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_14 | spl8_15)),
% 1.53/0.59    inference(subsumption_resolution,[],[f335,f253])).
% 1.53/0.59  fof(f253,plain,(
% 1.53/0.59    ~r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_15),
% 1.53/0.59    inference(avatar_component_clause,[],[f252])).
% 1.53/0.59  fof(f335,plain,(
% 1.53/0.59    r2_hidden(sK4(k1_xboole_0,k1_xboole_0),k1_xboole_0) | (~spl8_3 | ~spl8_5 | ~spl8_6 | ~spl8_13 | spl8_14 | spl8_15)),
% 1.53/0.59    inference(backward_demodulation,[],[f317,f332])).
% 1.53/0.59  fof(f332,plain,(
% 1.53/0.59    sK4(k1_xboole_0,k1_xboole_0) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)) | (~spl8_3 | ~spl8_6 | spl8_14 | spl8_15)),
% 1.53/0.59    inference(subsumption_resolution,[],[f325,f249])).
% 1.53/0.59  fof(f325,plain,(
% 1.53/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) | sK4(k1_xboole_0,k1_xboole_0) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)) | (~spl8_3 | ~spl8_6 | spl8_15)),
% 1.53/0.59    inference(resolution,[],[f154,f253])).
% 1.53/0.59  fof(f154,plain,(
% 1.53/0.59    ( ! [X1] : (r2_hidden(sK4(k1_xboole_0,X1),X1) | k2_relat_1(k1_xboole_0) = X1 | sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1))) ) | (~spl8_3 | ~spl8_6)),
% 1.53/0.59    inference(forward_demodulation,[],[f153,f133])).
% 1.53/0.59  fof(f153,plain,(
% 1.53/0.59    ( ! [X1] : (k2_relat_1(k1_xboole_0) = X1 | sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1)) | r2_hidden(sK4(sK2,X1),X1)) ) | (~spl8_3 | ~spl8_6)),
% 1.53/0.59    inference(forward_demodulation,[],[f141,f133])).
% 1.53/0.59  fof(f141,plain,(
% 1.53/0.59    ( ! [X1] : (sK4(k1_xboole_0,X1) = k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,X1)) | k2_relat_1(sK2) = X1 | r2_hidden(sK4(sK2,X1),X1)) ) | (~spl8_3 | ~spl8_6)),
% 1.53/0.59    inference(backward_demodulation,[],[f93,f133])).
% 1.53/0.59  fof(f317,plain,(
% 1.53/0.59    r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl8_5 | ~spl8_6 | ~spl8_13)),
% 1.53/0.59    inference(resolution,[],[f305,f280])).
% 1.53/0.59  fof(f280,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(X0,k1_xboole_0)) ) | (~spl8_5 | ~spl8_6)),
% 1.53/0.59    inference(backward_demodulation,[],[f229,f109])).
% 1.53/0.59  fof(f229,plain,(
% 1.53/0.59    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(X0,sK1)) ) | ~spl8_6),
% 1.53/0.59    inference(resolution,[],[f224,f59])).
% 1.53/0.59  fof(f224,plain,(
% 1.53/0.59    r1_tarski(k2_relat_1(k1_xboole_0),sK1) | ~spl8_6),
% 1.53/0.59    inference(subsumption_resolution,[],[f223,f142])).
% 1.53/0.59  fof(f142,plain,(
% 1.53/0.59    v1_relat_1(k1_xboole_0) | ~spl8_6),
% 1.53/0.59    inference(backward_demodulation,[],[f100,f133])).
% 1.53/0.59  fof(f223,plain,(
% 1.53/0.59    r1_tarski(k2_relat_1(k1_xboole_0),sK1) | ~v1_relat_1(k1_xboole_0) | ~spl8_6),
% 1.53/0.59    inference(resolution,[],[f209,f57])).
% 1.53/0.59  fof(f209,plain,(
% 1.53/0.59    v5_relat_1(k1_xboole_0,sK1) | ~spl8_6),
% 1.53/0.59    inference(forward_demodulation,[],[f97,f133])).
% 1.53/0.59  fof(f305,plain,(
% 1.53/0.59    r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (~spl8_6 | ~spl8_13)),
% 1.53/0.59    inference(subsumption_resolution,[],[f304,f142])).
% 1.53/0.59  fof(f304,plain,(
% 1.53/0.59    r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | (~spl8_6 | ~spl8_13)),
% 1.53/0.59    inference(subsumption_resolution,[],[f302,f139])).
% 1.53/0.59  fof(f139,plain,(
% 1.53/0.59    v1_funct_1(k1_xboole_0) | ~spl8_6),
% 1.53/0.59    inference(backward_demodulation,[],[f43,f133])).
% 1.53/0.59  fof(f302,plain,(
% 1.53/0.59    r2_hidden(k1_funct_1(k1_xboole_0,sK5(k1_xboole_0,k1_xboole_0)),k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~spl8_13),
% 1.53/0.59    inference(resolution,[],[f205,f73])).
% 1.53/0.59  fof(f205,plain,(
% 1.53/0.59    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~spl8_13),
% 1.53/0.59    inference(avatar_component_clause,[],[f203])).
% 1.53/0.59  fof(f138,plain,(
% 1.53/0.59    spl8_6 | spl8_7 | ~spl8_5),
% 1.53/0.59    inference(avatar_split_clause,[],[f129,f107,f135,f131])).
% 1.53/0.59  fof(f129,plain,(
% 1.53/0.59    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl8_5),
% 1.53/0.59    inference(subsumption_resolution,[],[f122,f113])).
% 1.53/0.59  fof(f113,plain,(
% 1.53/0.59    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_5),
% 1.53/0.59    inference(backward_demodulation,[],[f44,f109])).
% 1.53/0.59  fof(f122,plain,(
% 1.53/0.59    ~v1_funct_2(sK2,sK0,k1_xboole_0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl8_5),
% 1.53/0.59    inference(resolution,[],[f114,f78])).
% 1.53/0.59  fof(f78,plain,(
% 1.53/0.59    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 1.53/0.59    inference(equality_resolution,[],[f70])).
% 1.53/0.59  fof(f70,plain,(
% 1.53/0.59    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.53/0.59    inference(cnf_transformation,[],[f42])).
% 1.53/0.59  fof(f114,plain,(
% 1.53/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl8_5),
% 1.53/0.59    inference(backward_demodulation,[],[f45,f109])).
% 1.53/0.59  fof(f112,plain,(
% 1.53/0.59    spl8_1),
% 1.53/0.59    inference(avatar_contradiction_clause,[],[f111])).
% 1.53/0.59  fof(f111,plain,(
% 1.53/0.59    $false | spl8_1),
% 1.53/0.59    inference(subsumption_resolution,[],[f100,f86])).
% 1.53/0.59  fof(f86,plain,(
% 1.53/0.59    ~v1_relat_1(sK2) | spl8_1),
% 1.53/0.59    inference(avatar_component_clause,[],[f84])).
% 1.53/0.59  fof(f84,plain,(
% 1.53/0.59    spl8_1 <=> v1_relat_1(sK2)),
% 1.53/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.53/0.59  fof(f94,plain,(
% 1.53/0.59    ~spl8_1 | spl8_3),
% 1.53/0.59    inference(avatar_split_clause,[],[f82,f92,f84])).
% 1.53/0.59  fof(f82,plain,(
% 1.53/0.59    ( ! [X1] : (sK4(sK2,X1) = k1_funct_1(sK2,sK5(sK2,X1)) | r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1 | ~v1_relat_1(sK2)) )),
% 1.53/0.59    inference(resolution,[],[f43,f54])).
% 1.53/0.59  fof(f54,plain,(
% 1.53/0.59    ( ! [X0,X1] : (~v1_funct_1(X0) | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 1.53/0.59    inference(cnf_transformation,[],[f36])).
% 1.53/0.59  fof(f90,plain,(
% 1.53/0.59    ~spl8_1 | spl8_2),
% 1.53/0.59    inference(avatar_split_clause,[],[f81,f88,f84])).
% 1.53/0.59  fof(f81,plain,(
% 1.53/0.59    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) )),
% 1.53/0.59    inference(resolution,[],[f43,f53])).
% 1.53/0.59  % SZS output end Proof for theBenchmark
% 1.53/0.59  % (13444)------------------------------
% 1.53/0.59  % (13444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.59  % (13444)Termination reason: Refutation
% 1.53/0.59  
% 1.53/0.59  % (13444)Memory used [KB]: 11001
% 1.53/0.59  % (13444)Time elapsed: 0.148 s
% 1.53/0.59  % (13444)------------------------------
% 1.53/0.59  % (13444)------------------------------
% 1.53/0.59  % (13435)Success in time 0.224 s
%------------------------------------------------------------------------------
