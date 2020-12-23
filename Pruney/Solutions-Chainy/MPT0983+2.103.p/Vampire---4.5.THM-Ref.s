%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:49 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 429 expanded)
%              Number of leaves         :   42 ( 149 expanded)
%              Depth                    :   14
%              Number of atoms          :  606 (1828 expanded)
%              Number of equality atoms :   77 ( 198 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f884,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f214,f286,f289,f367,f369,f371,f374,f377,f512,f528,f530,f534,f584,f600,f708,f790,f807,f834,f867,f876,f879])).

fof(f879,plain,
    ( ~ spl5_38
    | ~ spl5_39
    | spl5_2
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f877,f723,f104,f755,f751])).

fof(f751,plain,
    ( spl5_38
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f755,plain,
    ( spl5_39
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f104,plain,
    ( spl5_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f723,plain,
    ( spl5_35
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f877,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_35 ),
    inference(superposition,[],[f91,f724])).

fof(f724,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f723])).

fof(f91,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f876,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f871])).

fof(f871,plain,
    ( $false
    | spl5_41 ),
    inference(resolution,[],[f866,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f866,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl5_41 ),
    inference(avatar_component_clause,[],[f864])).

fof(f864,plain,
    ( spl5_41
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f867,plain,
    ( ~ spl5_38
    | ~ spl5_41
    | ~ spl5_35
    | spl5_39 ),
    inference(avatar_split_clause,[],[f862,f755,f723,f864,f751])).

fof(f862,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_35
    | spl5_39 ),
    inference(forward_demodulation,[],[f760,f724])).

fof(f760,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl5_39 ),
    inference(resolution,[],[f757,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f757,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_39 ),
    inference(avatar_component_clause,[],[f755])).

fof(f834,plain,
    ( ~ spl5_15
    | spl5_35
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f832,f701,f723,f364])).

fof(f364,plain,
    ( spl5_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f701,plain,
    ( spl5_31
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f832,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_31 ),
    inference(superposition,[],[f81,f703])).

fof(f703,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f701])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f807,plain,
    ( ~ spl5_9
    | spl5_32 ),
    inference(avatar_contradiction_clause,[],[f805])).

fof(f805,plain,
    ( $false
    | ~ spl5_9
    | spl5_32 ),
    inference(resolution,[],[f707,f378])).

fof(f378,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f58,f285])).

fof(f285,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl5_9
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f58,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f707,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl5_32
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f790,plain,(
    spl5_38 ),
    inference(avatar_contradiction_clause,[],[f786])).

fof(f786,plain,
    ( $false
    | spl5_38 ),
    inference(resolution,[],[f759,f57])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f759,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_38 ),
    inference(resolution,[],[f753,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f753,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f751])).

fof(f708,plain,
    ( ~ spl5_14
    | ~ spl5_28
    | ~ spl5_15
    | ~ spl5_12
    | ~ spl5_27
    | ~ spl5_13
    | spl5_31
    | ~ spl5_32
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f699,f283,f705,f701,f356,f495,f352,f364,f499,f360])).

fof(f360,plain,
    ( spl5_14
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f499,plain,
    ( spl5_28
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f352,plain,
    ( spl5_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f495,plain,
    ( spl5_27
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f356,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f699,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_9 ),
    inference(superposition,[],[f82,f285])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f600,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(resolution,[],[f590,f167])).

fof(f167,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f90,f135])).

fof(f135,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(resolution,[],[f130,f92])).

fof(f130,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k6_partfun1(k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f121,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f118,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f118,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f116,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f83,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f121,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k6_partfun1(k1_xboole_0))
      | k6_partfun1(k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f119,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f119,plain,(
    ! [X0] : r1_tarski(k6_partfun1(k1_xboole_0),X0) ),
    inference(resolution,[],[f117,f73])).

fof(f117,plain,(
    ! [X0] : ~ r2_hidden(X0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[],[f116,f110])).

fof(f110,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f64,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f90,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f62,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f590,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f102,f588])).

fof(f588,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f587,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f587,plain,
    ( sK2 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl5_3
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f209,f434])).

fof(f434,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl5_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f209,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_3
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f102,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f584,plain,
    ( spl5_4
    | ~ spl5_19 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl5_4
    | ~ spl5_19 ),
    inference(resolution,[],[f563,f144])).

fof(f144,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f119,f135])).

fof(f563,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_4
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f541,f95])).

fof(f541,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2)
    | spl5_4
    | ~ spl5_19 ),
    inference(backward_demodulation,[],[f213,f434])).

fof(f213,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl5_4
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f534,plain,
    ( ~ spl5_12
    | ~ spl5_27
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_28
    | ~ spl5_15
    | spl5_1
    | spl5_19
    | ~ spl5_29
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f492,f283,f503,f432,f100,f364,f499,f360,f356,f495,f352])).

fof(f503,plain,
    ( spl5_29
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f492,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_9 ),
    inference(superposition,[],[f84,f285])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f530,plain,(
    spl5_28 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl5_28 ),
    inference(resolution,[],[f501,f56])).

fof(f56,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f501,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f499])).

fof(f528,plain,(
    spl5_27 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl5_27 ),
    inference(resolution,[],[f497,f53])).

fof(f53,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f497,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f495])).

fof(f512,plain,(
    spl5_29 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl5_29 ),
    inference(resolution,[],[f505,f90])).

fof(f505,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f503])).

fof(f377,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f366,f57])).

fof(f366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f364])).

fof(f374,plain,(
    spl5_13 ),
    inference(avatar_contradiction_clause,[],[f372])).

fof(f372,plain,
    ( $false
    | spl5_13 ),
    inference(resolution,[],[f358,f54])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f358,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f356])).

fof(f371,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f370])).

fof(f370,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f362,f55])).

fof(f55,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f362,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f360])).

fof(f369,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl5_12 ),
    inference(resolution,[],[f354,f52])).

fof(f52,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f354,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f352])).

fof(f367,plain,
    ( ~ spl5_12
    | ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15
    | spl5_7 ),
    inference(avatar_split_clause,[],[f349,f275,f364,f360,f356,f352])).

fof(f275,plain,
    ( spl5_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f349,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_7 ),
    inference(resolution,[],[f277,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f277,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f275])).

fof(f289,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f281,f64])).

fof(f281,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl5_8
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f286,plain,
    ( ~ spl5_7
    | ~ spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f271,f283,f279,f275])).

fof(f271,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f86,f58])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f214,plain,
    ( spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f201,f211,f207])).

fof(f201,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f114,f54])).

fof(f114,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ r1_tarski(X3,X4)
      | X3 = X4 ) ),
    inference(resolution,[],[f71,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f59,f104,f100])).

fof(f59,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:21:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (29290)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (29298)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.51  % (29307)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (29291)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.52  % (29292)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (29293)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.54  % (29289)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.54  % (29294)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.22/0.54  % (29308)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.22/0.54  % (29306)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.22/0.54  % (29288)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.22/0.54  % (29311)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.54  % (29300)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (29317)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.39/0.55  % (29296)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.55  % (29314)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.55  % (29309)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.55  % (29315)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (29305)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.55  % (29312)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.56  % (29302)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.56  % (29305)Refutation not found, incomplete strategy% (29305)------------------------------
% 1.39/0.56  % (29305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (29305)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (29305)Memory used [KB]: 10746
% 1.39/0.56  % (29305)Time elapsed: 0.150 s
% 1.39/0.56  % (29305)------------------------------
% 1.39/0.56  % (29305)------------------------------
% 1.39/0.56  % (29301)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.56  % (29316)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.56  % (29299)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.56  % (29313)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.56  % (29303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.56  % (29295)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.56  % (29304)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.57  % (29300)Refutation found. Thanks to Tanya!
% 1.39/0.57  % SZS status Theorem for theBenchmark
% 1.39/0.57  % SZS output start Proof for theBenchmark
% 1.39/0.57  fof(f884,plain,(
% 1.39/0.57    $false),
% 1.39/0.57    inference(avatar_sat_refutation,[],[f107,f214,f286,f289,f367,f369,f371,f374,f377,f512,f528,f530,f534,f584,f600,f708,f790,f807,f834,f867,f876,f879])).
% 1.39/0.57  fof(f879,plain,(
% 1.39/0.57    ~spl5_38 | ~spl5_39 | spl5_2 | ~spl5_35),
% 1.39/0.57    inference(avatar_split_clause,[],[f877,f723,f104,f755,f751])).
% 1.39/0.57  fof(f751,plain,(
% 1.39/0.57    spl5_38 <=> v1_relat_1(sK3)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.39/0.57  fof(f755,plain,(
% 1.39/0.57    spl5_39 <=> v5_relat_1(sK3,sK0)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.39/0.57  fof(f104,plain,(
% 1.39/0.57    spl5_2 <=> v2_funct_2(sK3,sK0)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.39/0.57  fof(f723,plain,(
% 1.39/0.57    spl5_35 <=> sK0 = k2_relat_1(sK3)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.39/0.57  fof(f877,plain,(
% 1.39/0.57    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_35),
% 1.39/0.57    inference(superposition,[],[f91,f724])).
% 1.39/0.57  fof(f724,plain,(
% 1.39/0.57    sK0 = k2_relat_1(sK3) | ~spl5_35),
% 1.39/0.57    inference(avatar_component_clause,[],[f723])).
% 1.39/0.57  fof(f91,plain,(
% 1.39/0.57    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.39/0.57    inference(equality_resolution,[],[f68])).
% 1.39/0.57  fof(f68,plain,(
% 1.39/0.57    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f41])).
% 1.39/0.57  fof(f41,plain,(
% 1.39/0.57    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.39/0.57    inference(nnf_transformation,[],[f24])).
% 1.39/0.57  fof(f24,plain,(
% 1.39/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.39/0.57    inference(flattening,[],[f23])).
% 1.39/0.57  fof(f23,plain,(
% 1.39/0.57    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.39/0.57    inference(ennf_transformation,[],[f12])).
% 1.39/0.57  fof(f12,axiom,(
% 1.39/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 1.39/0.57  fof(f876,plain,(
% 1.39/0.57    spl5_41),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f871])).
% 1.39/0.57  fof(f871,plain,(
% 1.39/0.57    $false | spl5_41),
% 1.39/0.57    inference(resolution,[],[f866,f92])).
% 1.39/0.57  fof(f92,plain,(
% 1.39/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.39/0.57    inference(equality_resolution,[],[f70])).
% 1.39/0.57  fof(f70,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.39/0.57    inference(cnf_transformation,[],[f43])).
% 1.39/0.57  fof(f43,plain,(
% 1.39/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.57    inference(flattening,[],[f42])).
% 1.39/0.57  fof(f42,plain,(
% 1.39/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.57    inference(nnf_transformation,[],[f3])).
% 1.39/0.57  fof(f3,axiom,(
% 1.39/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.57  fof(f866,plain,(
% 1.39/0.57    ~r1_tarski(sK0,sK0) | spl5_41),
% 1.39/0.57    inference(avatar_component_clause,[],[f864])).
% 1.39/0.57  fof(f864,plain,(
% 1.39/0.57    spl5_41 <=> r1_tarski(sK0,sK0)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.39/0.57  fof(f867,plain,(
% 1.39/0.57    ~spl5_38 | ~spl5_41 | ~spl5_35 | spl5_39),
% 1.39/0.57    inference(avatar_split_clause,[],[f862,f755,f723,f864,f751])).
% 1.39/0.57  fof(f862,plain,(
% 1.39/0.57    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | (~spl5_35 | spl5_39)),
% 1.39/0.57    inference(forward_demodulation,[],[f760,f724])).
% 1.39/0.57  fof(f760,plain,(
% 1.39/0.57    ~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl5_39),
% 1.39/0.57    inference(resolution,[],[f757,f66])).
% 1.39/0.57  fof(f66,plain,(
% 1.39/0.57    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f40])).
% 1.39/0.57  fof(f40,plain,(
% 1.39/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.39/0.57    inference(nnf_transformation,[],[f22])).
% 1.39/0.57  fof(f22,plain,(
% 1.39/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.57    inference(ennf_transformation,[],[f7])).
% 1.39/0.57  fof(f7,axiom,(
% 1.39/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 1.39/0.57  fof(f757,plain,(
% 1.39/0.57    ~v5_relat_1(sK3,sK0) | spl5_39),
% 1.39/0.57    inference(avatar_component_clause,[],[f755])).
% 1.39/0.57  fof(f834,plain,(
% 1.39/0.57    ~spl5_15 | spl5_35 | ~spl5_31),
% 1.39/0.57    inference(avatar_split_clause,[],[f832,f701,f723,f364])).
% 1.39/0.57  fof(f364,plain,(
% 1.39/0.57    spl5_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.39/0.57  fof(f701,plain,(
% 1.39/0.57    spl5_31 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.39/0.57  fof(f832,plain,(
% 1.39/0.57    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_31),
% 1.39/0.57    inference(superposition,[],[f81,f703])).
% 1.39/0.57  fof(f703,plain,(
% 1.39/0.57    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_31),
% 1.39/0.57    inference(avatar_component_clause,[],[f701])).
% 1.39/0.57  fof(f81,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f27])).
% 1.39/0.57  fof(f27,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(ennf_transformation,[],[f10])).
% 1.39/0.57  fof(f10,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.39/0.57  fof(f807,plain,(
% 1.39/0.57    ~spl5_9 | spl5_32),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f805])).
% 1.39/0.57  fof(f805,plain,(
% 1.39/0.57    $false | (~spl5_9 | spl5_32)),
% 1.39/0.57    inference(resolution,[],[f707,f378])).
% 1.39/0.57  fof(f378,plain,(
% 1.39/0.57    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl5_9),
% 1.39/0.57    inference(backward_demodulation,[],[f58,f285])).
% 1.39/0.57  fof(f285,plain,(
% 1.39/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl5_9),
% 1.39/0.57    inference(avatar_component_clause,[],[f283])).
% 1.39/0.57  fof(f283,plain,(
% 1.39/0.57    spl5_9 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.39/0.57  fof(f58,plain,(
% 1.39/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f39,plain,(
% 1.39/0.57    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.39/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f21,f38,f37])).
% 1.39/0.57  fof(f37,plain,(
% 1.39/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.39/0.57    introduced(choice_axiom,[])).
% 1.39/0.57  fof(f38,plain,(
% 1.39/0.57    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.39/0.57    introduced(choice_axiom,[])).
% 1.39/0.57  fof(f21,plain,(
% 1.39/0.57    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.57    inference(flattening,[],[f20])).
% 1.39/0.57  fof(f20,plain,(
% 1.39/0.57    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.57    inference(ennf_transformation,[],[f19])).
% 1.39/0.57  fof(f19,negated_conjecture,(
% 1.39/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.39/0.57    inference(negated_conjecture,[],[f18])).
% 1.39/0.57  fof(f18,conjecture,(
% 1.39/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 1.39/0.57  fof(f707,plain,(
% 1.39/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl5_32),
% 1.39/0.57    inference(avatar_component_clause,[],[f705])).
% 1.39/0.57  fof(f705,plain,(
% 1.39/0.57    spl5_32 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.39/0.57  fof(f790,plain,(
% 1.39/0.57    spl5_38),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f786])).
% 1.39/0.57  fof(f786,plain,(
% 1.39/0.57    $false | spl5_38),
% 1.39/0.57    inference(resolution,[],[f759,f57])).
% 1.39/0.57  fof(f57,plain,(
% 1.39/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f759,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_38),
% 1.39/0.57    inference(resolution,[],[f753,f80])).
% 1.39/0.57  fof(f80,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f26])).
% 1.39/0.57  fof(f26,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(ennf_transformation,[],[f9])).
% 1.39/0.57  fof(f9,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.39/0.57  fof(f753,plain,(
% 1.39/0.57    ~v1_relat_1(sK3) | spl5_38),
% 1.39/0.57    inference(avatar_component_clause,[],[f751])).
% 1.39/0.57  fof(f708,plain,(
% 1.39/0.57    ~spl5_14 | ~spl5_28 | ~spl5_15 | ~spl5_12 | ~spl5_27 | ~spl5_13 | spl5_31 | ~spl5_32 | ~spl5_9),
% 1.39/0.57    inference(avatar_split_clause,[],[f699,f283,f705,f701,f356,f495,f352,f364,f499,f360])).
% 1.39/0.57  fof(f360,plain,(
% 1.39/0.57    spl5_14 <=> v1_funct_1(sK3)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.39/0.57  fof(f499,plain,(
% 1.39/0.57    spl5_28 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.39/0.57  fof(f352,plain,(
% 1.39/0.57    spl5_12 <=> v1_funct_1(sK2)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.39/0.57  fof(f495,plain,(
% 1.39/0.57    spl5_27 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.39/0.57  fof(f356,plain,(
% 1.39/0.57    spl5_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.39/0.57  fof(f699,plain,(
% 1.39/0.57    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_9),
% 1.39/0.57    inference(superposition,[],[f82,f285])).
% 1.39/0.57  fof(f82,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f29])).
% 1.39/0.57  fof(f29,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.39/0.57    inference(flattening,[],[f28])).
% 1.39/0.57  fof(f28,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.39/0.57    inference(ennf_transformation,[],[f16])).
% 1.39/0.57  fof(f16,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.39/0.57  fof(f600,plain,(
% 1.39/0.57    spl5_1 | ~spl5_3 | ~spl5_19),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f599])).
% 1.39/0.57  fof(f599,plain,(
% 1.39/0.57    $false | (spl5_1 | ~spl5_3 | ~spl5_19)),
% 1.39/0.57    inference(resolution,[],[f590,f167])).
% 1.39/0.57  fof(f167,plain,(
% 1.39/0.57    v2_funct_1(k1_xboole_0)),
% 1.39/0.57    inference(superposition,[],[f90,f135])).
% 1.39/0.57  fof(f135,plain,(
% 1.39/0.57    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.39/0.57    inference(resolution,[],[f130,f92])).
% 1.39/0.57  fof(f130,plain,(
% 1.39/0.57    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k6_partfun1(k1_xboole_0) = X1) )),
% 1.39/0.57    inference(resolution,[],[f121,f122])).
% 1.39/0.57  fof(f122,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k1_xboole_0)) )),
% 1.39/0.57    inference(resolution,[],[f118,f73])).
% 1.39/0.57  fof(f73,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f47])).
% 1.39/0.57  fof(f47,plain,(
% 1.39/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f45,f46])).
% 1.39/0.57  fof(f46,plain,(
% 1.39/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.39/0.57    introduced(choice_axiom,[])).
% 1.39/0.57  fof(f45,plain,(
% 1.39/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.57    inference(rectify,[],[f44])).
% 1.39/0.57  fof(f44,plain,(
% 1.39/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.57    inference(nnf_transformation,[],[f25])).
% 1.39/0.57  fof(f25,plain,(
% 1.39/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.57    inference(ennf_transformation,[],[f1])).
% 1.39/0.57  fof(f1,axiom,(
% 1.39/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.57  fof(f118,plain,(
% 1.39/0.57    ( ! [X2,X1] : (~r2_hidden(X1,X2) | ~r1_tarski(X2,k1_xboole_0)) )),
% 1.39/0.57    inference(resolution,[],[f116,f76])).
% 1.39/0.57  fof(f76,plain,(
% 1.39/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f48])).
% 1.39/0.57  fof(f48,plain,(
% 1.39/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.57    inference(nnf_transformation,[],[f5])).
% 1.39/0.57  fof(f5,axiom,(
% 1.39/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.57  fof(f116,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.39/0.57    inference(resolution,[],[f83,f60])).
% 1.39/0.57  fof(f60,plain,(
% 1.39/0.57    v1_xboole_0(k1_xboole_0)),
% 1.39/0.57    inference(cnf_transformation,[],[f2])).
% 1.39/0.57  fof(f2,axiom,(
% 1.39/0.57    v1_xboole_0(k1_xboole_0)),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.39/0.57  fof(f83,plain,(
% 1.39/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f30])).
% 1.39/0.57  fof(f30,plain,(
% 1.39/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.39/0.57    inference(ennf_transformation,[],[f6])).
% 1.39/0.57  fof(f6,axiom,(
% 1.39/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.39/0.57  fof(f121,plain,(
% 1.39/0.57    ( ! [X0] : (~r1_tarski(X0,k6_partfun1(k1_xboole_0)) | k6_partfun1(k1_xboole_0) = X0) )),
% 1.39/0.57    inference(resolution,[],[f119,f71])).
% 1.39/0.57  fof(f71,plain,(
% 1.39/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f43])).
% 1.39/0.57  fof(f119,plain,(
% 1.39/0.57    ( ! [X0] : (r1_tarski(k6_partfun1(k1_xboole_0),X0)) )),
% 1.39/0.57    inference(resolution,[],[f117,f73])).
% 1.39/0.57  fof(f117,plain,(
% 1.39/0.57    ( ! [X0] : (~r2_hidden(X0,k6_partfun1(k1_xboole_0))) )),
% 1.39/0.57    inference(resolution,[],[f116,f110])).
% 1.39/0.57  fof(f110,plain,(
% 1.39/0.57    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 1.39/0.57    inference(superposition,[],[f64,f94])).
% 1.39/0.57  fof(f94,plain,(
% 1.39/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.57    inference(equality_resolution,[],[f79])).
% 1.39/0.57  fof(f79,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.57    inference(cnf_transformation,[],[f50])).
% 1.39/0.57  fof(f50,plain,(
% 1.39/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.57    inference(flattening,[],[f49])).
% 1.39/0.57  fof(f49,plain,(
% 1.39/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.57    inference(nnf_transformation,[],[f4])).
% 1.39/0.57  fof(f4,axiom,(
% 1.39/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.57  fof(f64,plain,(
% 1.39/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f14])).
% 1.39/0.57  fof(f14,axiom,(
% 1.39/0.57    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.39/0.57  fof(f90,plain,(
% 1.39/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.39/0.57    inference(definition_unfolding,[],[f61,f62])).
% 1.39/0.57  fof(f62,plain,(
% 1.39/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f15])).
% 1.39/0.57  fof(f15,axiom,(
% 1.39/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.39/0.57  fof(f61,plain,(
% 1.39/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f8])).
% 1.39/0.57  fof(f8,axiom,(
% 1.39/0.57    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 1.39/0.57  fof(f590,plain,(
% 1.39/0.57    ~v2_funct_1(k1_xboole_0) | (spl5_1 | ~spl5_3 | ~spl5_19)),
% 1.39/0.57    inference(backward_demodulation,[],[f102,f588])).
% 1.39/0.57  fof(f588,plain,(
% 1.39/0.57    k1_xboole_0 = sK2 | (~spl5_3 | ~spl5_19)),
% 1.39/0.57    inference(forward_demodulation,[],[f587,f95])).
% 1.39/0.57  fof(f95,plain,(
% 1.39/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.57    inference(equality_resolution,[],[f78])).
% 1.39/0.57  fof(f78,plain,(
% 1.39/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.39/0.57    inference(cnf_transformation,[],[f50])).
% 1.39/0.57  fof(f587,plain,(
% 1.39/0.57    sK2 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl5_3 | ~spl5_19)),
% 1.39/0.57    inference(forward_demodulation,[],[f209,f434])).
% 1.39/0.57  fof(f434,plain,(
% 1.39/0.57    k1_xboole_0 = sK0 | ~spl5_19),
% 1.39/0.57    inference(avatar_component_clause,[],[f432])).
% 1.39/0.57  fof(f432,plain,(
% 1.39/0.57    spl5_19 <=> k1_xboole_0 = sK0),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.39/0.57  fof(f209,plain,(
% 1.39/0.57    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_3),
% 1.39/0.57    inference(avatar_component_clause,[],[f207])).
% 1.39/0.57  fof(f207,plain,(
% 1.39/0.57    spl5_3 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.39/0.57  fof(f102,plain,(
% 1.39/0.57    ~v2_funct_1(sK2) | spl5_1),
% 1.39/0.57    inference(avatar_component_clause,[],[f100])).
% 1.39/0.57  fof(f100,plain,(
% 1.39/0.57    spl5_1 <=> v2_funct_1(sK2)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.39/0.57  fof(f584,plain,(
% 1.39/0.57    spl5_4 | ~spl5_19),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f579])).
% 1.39/0.57  fof(f579,plain,(
% 1.39/0.57    $false | (spl5_4 | ~spl5_19)),
% 1.39/0.57    inference(resolution,[],[f563,f144])).
% 1.39/0.57  fof(f144,plain,(
% 1.39/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.57    inference(backward_demodulation,[],[f119,f135])).
% 1.39/0.57  fof(f563,plain,(
% 1.39/0.57    ~r1_tarski(k1_xboole_0,sK2) | (spl5_4 | ~spl5_19)),
% 1.39/0.57    inference(forward_demodulation,[],[f541,f95])).
% 1.39/0.57  fof(f541,plain,(
% 1.39/0.57    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK2) | (spl5_4 | ~spl5_19)),
% 1.39/0.57    inference(backward_demodulation,[],[f213,f434])).
% 1.39/0.57  fof(f213,plain,(
% 1.39/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl5_4),
% 1.39/0.57    inference(avatar_component_clause,[],[f211])).
% 1.39/0.57  fof(f211,plain,(
% 1.39/0.57    spl5_4 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.39/0.57  fof(f534,plain,(
% 1.39/0.57    ~spl5_12 | ~spl5_27 | ~spl5_13 | ~spl5_14 | ~spl5_28 | ~spl5_15 | spl5_1 | spl5_19 | ~spl5_29 | ~spl5_9),
% 1.39/0.57    inference(avatar_split_clause,[],[f492,f283,f503,f432,f100,f364,f499,f360,f356,f495,f352])).
% 1.39/0.57  fof(f503,plain,(
% 1.39/0.57    spl5_29 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.39/0.57  fof(f492,plain,(
% 1.39/0.57    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_9),
% 1.39/0.57    inference(superposition,[],[f84,f285])).
% 1.39/0.57  fof(f84,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f32])).
% 1.39/0.57  fof(f32,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.39/0.57    inference(flattening,[],[f31])).
% 1.39/0.57  fof(f31,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.39/0.57    inference(ennf_transformation,[],[f17])).
% 1.39/0.57  fof(f17,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 1.39/0.57  fof(f530,plain,(
% 1.39/0.57    spl5_28),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f529])).
% 1.39/0.57  fof(f529,plain,(
% 1.39/0.57    $false | spl5_28),
% 1.39/0.57    inference(resolution,[],[f501,f56])).
% 1.39/0.57  fof(f56,plain,(
% 1.39/0.57    v1_funct_2(sK3,sK1,sK0)),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f501,plain,(
% 1.39/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl5_28),
% 1.39/0.57    inference(avatar_component_clause,[],[f499])).
% 1.39/0.57  fof(f528,plain,(
% 1.39/0.57    spl5_27),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f527])).
% 1.39/0.57  fof(f527,plain,(
% 1.39/0.57    $false | spl5_27),
% 1.39/0.57    inference(resolution,[],[f497,f53])).
% 1.39/0.57  fof(f53,plain,(
% 1.39/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f497,plain,(
% 1.39/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl5_27),
% 1.39/0.57    inference(avatar_component_clause,[],[f495])).
% 1.39/0.57  fof(f512,plain,(
% 1.39/0.57    spl5_29),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f511])).
% 1.39/0.57  fof(f511,plain,(
% 1.39/0.57    $false | spl5_29),
% 1.39/0.57    inference(resolution,[],[f505,f90])).
% 1.39/0.57  fof(f505,plain,(
% 1.39/0.57    ~v2_funct_1(k6_partfun1(sK0)) | spl5_29),
% 1.39/0.57    inference(avatar_component_clause,[],[f503])).
% 1.39/0.57  fof(f377,plain,(
% 1.39/0.57    spl5_15),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f375])).
% 1.39/0.57  fof(f375,plain,(
% 1.39/0.57    $false | spl5_15),
% 1.39/0.57    inference(resolution,[],[f366,f57])).
% 1.39/0.57  fof(f366,plain,(
% 1.39/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_15),
% 1.39/0.57    inference(avatar_component_clause,[],[f364])).
% 1.39/0.57  fof(f374,plain,(
% 1.39/0.57    spl5_13),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f372])).
% 1.39/0.57  fof(f372,plain,(
% 1.39/0.57    $false | spl5_13),
% 1.39/0.57    inference(resolution,[],[f358,f54])).
% 1.39/0.57  fof(f54,plain,(
% 1.39/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f358,plain,(
% 1.39/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_13),
% 1.39/0.57    inference(avatar_component_clause,[],[f356])).
% 1.39/0.57  fof(f371,plain,(
% 1.39/0.57    spl5_14),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f370])).
% 1.39/0.57  fof(f370,plain,(
% 1.39/0.57    $false | spl5_14),
% 1.39/0.57    inference(resolution,[],[f362,f55])).
% 1.39/0.57  fof(f55,plain,(
% 1.39/0.57    v1_funct_1(sK3)),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f362,plain,(
% 1.39/0.57    ~v1_funct_1(sK3) | spl5_14),
% 1.39/0.57    inference(avatar_component_clause,[],[f360])).
% 1.39/0.57  fof(f369,plain,(
% 1.39/0.57    spl5_12),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f368])).
% 1.39/0.57  fof(f368,plain,(
% 1.39/0.57    $false | spl5_12),
% 1.39/0.57    inference(resolution,[],[f354,f52])).
% 1.39/0.57  fof(f52,plain,(
% 1.39/0.57    v1_funct_1(sK2)),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  fof(f354,plain,(
% 1.39/0.57    ~v1_funct_1(sK2) | spl5_12),
% 1.39/0.57    inference(avatar_component_clause,[],[f352])).
% 1.39/0.57  fof(f367,plain,(
% 1.39/0.57    ~spl5_12 | ~spl5_13 | ~spl5_14 | ~spl5_15 | spl5_7),
% 1.39/0.57    inference(avatar_split_clause,[],[f349,f275,f364,f360,f356,f352])).
% 1.39/0.57  fof(f275,plain,(
% 1.39/0.57    spl5_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.39/0.57  fof(f349,plain,(
% 1.39/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl5_7),
% 1.39/0.57    inference(resolution,[],[f277,f89])).
% 1.39/0.57  fof(f89,plain,(
% 1.39/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.39/0.57    inference(cnf_transformation,[],[f36])).
% 1.39/0.57  fof(f36,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.39/0.57    inference(flattening,[],[f35])).
% 1.39/0.57  fof(f35,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.39/0.57    inference(ennf_transformation,[],[f13])).
% 1.39/0.57  fof(f13,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.39/0.57  fof(f277,plain,(
% 1.39/0.57    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_7),
% 1.39/0.57    inference(avatar_component_clause,[],[f275])).
% 1.39/0.57  fof(f289,plain,(
% 1.39/0.57    spl5_8),
% 1.39/0.57    inference(avatar_contradiction_clause,[],[f287])).
% 1.39/0.57  fof(f287,plain,(
% 1.39/0.57    $false | spl5_8),
% 1.39/0.57    inference(resolution,[],[f281,f64])).
% 1.39/0.57  fof(f281,plain,(
% 1.39/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_8),
% 1.39/0.57    inference(avatar_component_clause,[],[f279])).
% 1.39/0.57  fof(f279,plain,(
% 1.39/0.57    spl5_8 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.39/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.39/0.57  fof(f286,plain,(
% 1.39/0.57    ~spl5_7 | ~spl5_8 | spl5_9),
% 1.39/0.57    inference(avatar_split_clause,[],[f271,f283,f279,f275])).
% 1.39/0.57  fof(f271,plain,(
% 1.39/0.57    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.39/0.57    inference(resolution,[],[f86,f58])).
% 1.39/0.57  fof(f86,plain,(
% 1.39/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f51])).
% 1.39/0.57  fof(f51,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(nnf_transformation,[],[f34])).
% 1.39/0.57  fof(f34,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.57    inference(flattening,[],[f33])).
% 1.39/0.57  fof(f33,plain,(
% 1.39/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.39/0.57    inference(ennf_transformation,[],[f11])).
% 1.39/0.57  fof(f11,axiom,(
% 1.39/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.39/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.39/0.57  fof(f214,plain,(
% 1.39/0.57    spl5_3 | ~spl5_4),
% 1.39/0.57    inference(avatar_split_clause,[],[f201,f211,f207])).
% 1.39/0.57  fof(f201,plain,(
% 1.39/0.57    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.57    inference(resolution,[],[f114,f54])).
% 1.39/0.57  fof(f114,plain,(
% 1.39/0.57    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~r1_tarski(X3,X4) | X3 = X4) )),
% 1.39/0.57    inference(resolution,[],[f71,f75])).
% 1.39/0.57  fof(f75,plain,(
% 1.39/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.39/0.57    inference(cnf_transformation,[],[f48])).
% 1.39/0.57  fof(f107,plain,(
% 1.39/0.57    ~spl5_1 | ~spl5_2),
% 1.39/0.57    inference(avatar_split_clause,[],[f59,f104,f100])).
% 1.39/0.57  fof(f59,plain,(
% 1.39/0.57    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.39/0.57    inference(cnf_transformation,[],[f39])).
% 1.39/0.57  % SZS output end Proof for theBenchmark
% 1.39/0.57  % (29300)------------------------------
% 1.39/0.57  % (29300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.57  % (29300)Termination reason: Refutation
% 1.39/0.57  
% 1.39/0.57  % (29300)Memory used [KB]: 6524
% 1.39/0.57  % (29300)Time elapsed: 0.167 s
% 1.39/0.57  % (29300)------------------------------
% 1.39/0.57  % (29300)------------------------------
% 1.39/0.58  % (29287)Success in time 0.208 s
%------------------------------------------------------------------------------
