%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 314 expanded)
%              Number of leaves         :   24 ( 114 expanded)
%              Depth                    :   14
%              Number of atoms          :  447 (1982 expanded)
%              Number of equality atoms :   64 (  80 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f227,f304,f330,f331,f351])).

fof(f351,plain,(
    ~ spl9_8 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f342,f140])).

fof(f140,plain,(
    ~ v5_relat_1(sK7,sK4) ),
    inference(subsumption_resolution,[],[f138,f105])).

fof(f105,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
        | ~ m1_subset_1(X4,sK5) )
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7)
    & ~ v1_xboole_0(sK6)
    & ~ v1_xboole_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f45,f44,f43])).

fof(f43,plain,
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
              ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                  | ~ m1_subset_1(X4,sK5) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
              & v1_funct_2(X3,sK5,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK5,X2,X3),sK4)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4)
                | ~ m1_subset_1(X4,sK5) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2)))
            & v1_funct_2(X3,sK5,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
              | ~ m1_subset_1(X4,sK5) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
          & v1_funct_2(X3,sK5,sK6)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK5,sK6,X3),sK4)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4)
            | ~ m1_subset_1(X4,sK5) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
        & v1_funct_2(X3,sK5,sK6)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
          | ~ m1_subset_1(X4,sK5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f138,plain,
    ( ~ v5_relat_1(sK7,sK4)
    | ~ v1_relat_1(sK7) ),
    inference(resolution,[],[f137,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f137,plain,(
    ~ r1_tarski(k2_relat_1(sK7),sK4) ),
    inference(subsumption_resolution,[],[f136,f63])).

fof(f136,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),sK4)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(superposition,[],[f65,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f65,plain,(
    ~ r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f342,plain,
    ( v5_relat_1(sK7,sK4)
    | ~ spl9_8 ),
    inference(resolution,[],[f302,f133])).

fof(f133,plain,(
    ! [X6,X8,X7] :
      ( ~ sP3(X6,X7,X8)
      | v5_relat_1(X8,X6) ) ),
    inference(resolution,[],[f92,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP3(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f302,plain,
    ( sP3(sK4,sK5,sK7)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl9_8
  <=> sP3(sK4,sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f331,plain,
    ( spl9_8
    | ~ spl9_5
    | spl9_7 ),
    inference(avatar_split_clause,[],[f306,f296,f220,f300])).

fof(f220,plain,
    ( spl9_5
  <=> sK5 = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f296,plain,
    ( spl9_7
  <=> m1_subset_1(sK8(sK5,sK4,sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f306,plain,
    ( sP3(sK4,sK5,sK7)
    | ~ spl9_5
    | spl9_7 ),
    inference(resolution,[],[f305,f231])).

fof(f231,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK5,X0,sK7),sK5)
        | sP3(X0,sK5,sK7) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f230,f105])).

fof(f230,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK5,X0,sK7),sK5)
        | sP3(X0,sK5,sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f229,f61])).

fof(f61,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f229,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK5,X0,sK7),sK5)
        | sP3(X0,sK5,sK7)
        | ~ v1_funct_1(sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_5 ),
    inference(superposition,[],[f104,f222])).

fof(f222,plain,
    ( sK5 = k1_relat_1(sK7)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f220])).

fof(f104,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
        & r2_hidden(sK8(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP3(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f32,f41])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f305,plain,
    ( ~ r2_hidden(sK8(sK5,sK4,sK7),sK5)
    | spl9_7 ),
    inference(resolution,[],[f298,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f298,plain,
    ( ~ m1_subset_1(sK8(sK5,sK4,sK7),sK5)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f296])).

fof(f330,plain,(
    ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f323,f142])).

fof(f142,plain,(
    ~ v5_relat_1(sK7,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f141,f105])).

fof(f141,plain,
    ( ~ v5_relat_1(sK7,k1_xboole_0)
    | ~ v1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f139,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f139,plain,
    ( ~ r1_tarski(k1_xboole_0,sK4)
    | ~ v5_relat_1(sK7,k1_xboole_0)
    | ~ v1_relat_1(sK7) ),
    inference(superposition,[],[f137,f117])).

fof(f117,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f110,f69])).

fof(f110,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f74,f66])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f323,plain,
    ( v5_relat_1(sK7,k1_xboole_0)
    | ~ spl9_6 ),
    inference(backward_demodulation,[],[f118,f317])).

fof(f317,plain,
    ( k1_xboole_0 = sK6
    | ~ spl9_6 ),
    inference(resolution,[],[f226,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f226,plain,
    ( sP0(sK5,sK6)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl9_6
  <=> sP0(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f118,plain,(
    v5_relat_1(sK7,sK6) ),
    inference(resolution,[],[f79,f63])).

fof(f304,plain,
    ( spl9_8
    | ~ spl9_7
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f290,f220,f296,f300])).

fof(f290,plain,
    ( ~ m1_subset_1(sK8(sK5,sK4,sK7),sK5)
    | sP3(sK4,sK5,sK7)
    | ~ spl9_5 ),
    inference(resolution,[],[f288,f234])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0)
        | sP3(X0,sK5,sK7) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f233,f105])).

fof(f233,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0)
        | sP3(X0,sK5,sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f232,f61])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0)
        | sP3(X0,sK5,sK7)
        | ~ v1_funct_1(sK7)
        | ~ v1_relat_1(sK7) )
    | ~ spl9_5 ),
    inference(superposition,[],[f103,f222])).

fof(f103,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1)
      | sP3(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f288,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5) ) ),
    inference(subsumption_resolution,[],[f287,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f287,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f286,f61])).

fof(f286,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f285,f62])).

fof(f62,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f46])).

fof(f285,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(subsumption_resolution,[],[f284,f63])).

fof(f284,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(duplicate_literal_removal,[],[f283])).

fof(f283,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK7,X0),sK4)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(X0,sK5)
      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK7,sK5,sK6)
      | ~ v1_funct_1(sK7)
      | v1_xboole_0(sK5) ) ),
    inference(superposition,[],[f64,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f64,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4)
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f227,plain,
    ( spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f218,f224,f220])).

fof(f218,plain,
    ( sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(subsumption_resolution,[],[f214,f62])).

fof(f214,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | sP0(sK5,sK6)
    | sK5 = k1_relat_1(sK7) ),
    inference(resolution,[],[f185,f63])).

fof(f185,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f183,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f28,f39,f38,f37])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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

fof(f183,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f82,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (10585)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (10586)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (10592)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (10586)Refutation not found, incomplete strategy% (10586)------------------------------
% 0.21/0.53  % (10586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (10586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (10586)Memory used [KB]: 10618
% 0.21/0.53  % (10586)Time elapsed: 0.105 s
% 0.21/0.53  % (10586)------------------------------
% 0.21/0.53  % (10586)------------------------------
% 0.21/0.53  % (10595)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (10587)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (10583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (10596)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (10587)Refutation not found, incomplete strategy% (10587)------------------------------
% 0.21/0.54  % (10587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10587)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10587)Memory used [KB]: 1663
% 0.21/0.54  % (10587)Time elapsed: 0.097 s
% 0.21/0.54  % (10587)------------------------------
% 0.21/0.54  % (10587)------------------------------
% 0.21/0.54  % (10593)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (10582)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (10584)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (10603)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (10602)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (10599)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.54  % (10598)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (10584)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (10590)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (10594)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (10604)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (10601)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (10591)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (10591)Refutation not found, incomplete strategy% (10591)------------------------------
% 0.21/0.55  % (10591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10591)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10591)Memory used [KB]: 10746
% 0.21/0.55  % (10591)Time elapsed: 0.128 s
% 0.21/0.55  % (10591)------------------------------
% 0.21/0.55  % (10591)------------------------------
% 0.21/0.55  % (10605)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (10589)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (10600)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (10597)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (10581)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f352,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f227,f304,f330,f331,f351])).
% 0.21/0.56  fof(f351,plain,(
% 0.21/0.56    ~spl9_8),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f350])).
% 0.21/0.56  fof(f350,plain,(
% 0.21/0.56    $false | ~spl9_8),
% 0.21/0.56    inference(subsumption_resolution,[],[f342,f140])).
% 0.21/0.56  fof(f140,plain,(
% 0.21/0.56    ~v5_relat_1(sK7,sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f138,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    v1_relat_1(sK7)),
% 0.21/0.56    inference(resolution,[],[f75,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ((~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)) & ~v1_xboole_0(sK6)) & ~v1_xboole_0(sK5)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f45,f44,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK5))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK5,X2,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,X2,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,X2))) & v1_funct_2(X3,sK5,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) & ~v1_xboole_0(sK6))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ? [X3] : (~r1_tarski(k2_relset_1(sK5,sK6,X3),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,X3,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(X3,sK5,sK6) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4) & ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f15])).
% 0.21/0.56  fof(f15,conjecture,(
% 0.21/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ~v5_relat_1(sK7,sK4) | ~v1_relat_1(sK7)),
% 0.21/0.56    inference(resolution,[],[f137,f69])).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK7),sK4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f136,f63])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ~r1_tarski(k2_relat_1(sK7),sK4) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 0.21/0.56    inference(superposition,[],[f65,f77])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ~r1_tarski(k2_relset_1(sK5,sK6,sK7),sK4)),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f342,plain,(
% 0.21/0.56    v5_relat_1(sK7,sK4) | ~spl9_8),
% 0.21/0.56    inference(resolution,[],[f302,f133])).
% 0.21/0.56  fof(f133,plain,(
% 0.21/0.56    ( ! [X6,X8,X7] : (~sP3(X6,X7,X8) | v5_relat_1(X8,X6)) )),
% 0.21/0.56    inference(resolution,[],[f92,f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP3(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP3(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP3(X1,X0,X2))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.56  fof(f302,plain,(
% 0.21/0.56    sP3(sK4,sK5,sK7) | ~spl9_8),
% 0.21/0.56    inference(avatar_component_clause,[],[f300])).
% 0.21/0.56  fof(f300,plain,(
% 0.21/0.56    spl9_8 <=> sP3(sK4,sK5,sK7)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.56  fof(f331,plain,(
% 0.21/0.56    spl9_8 | ~spl9_5 | spl9_7),
% 0.21/0.56    inference(avatar_split_clause,[],[f306,f296,f220,f300])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    spl9_5 <=> sK5 = k1_relat_1(sK7)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.56  fof(f296,plain,(
% 0.21/0.56    spl9_7 <=> m1_subset_1(sK8(sK5,sK4,sK7),sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.56  fof(f306,plain,(
% 0.21/0.56    sP3(sK4,sK5,sK7) | (~spl9_5 | spl9_7)),
% 0.21/0.56    inference(resolution,[],[f305,f231])).
% 0.21/0.56  fof(f231,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK8(sK5,X0,sK7),sK5) | sP3(X0,sK5,sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f230,f105])).
% 0.21/0.56  fof(f230,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK8(sK5,X0,sK7),sK5) | sP3(X0,sK5,sK7) | ~v1_relat_1(sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f229,f61])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    v1_funct_1(sK7)),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(sK8(sK5,X0,sK7),sK5) | sP3(X0,sK5,sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f104,f222])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    sK5 = k1_relat_1(sK7) | ~spl9_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f220])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    ( ! [X2,X1] : (r2_hidden(sK8(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | r2_hidden(sK8(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP3(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f42,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) & r2_hidden(sK8(X0,X1,X2),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP3(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(definition_folding,[],[f32,f41])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    ~r2_hidden(sK8(sK5,sK4,sK7),sK5) | spl9_7),
% 0.21/0.56    inference(resolution,[],[f298,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.56  fof(f298,plain,(
% 0.21/0.56    ~m1_subset_1(sK8(sK5,sK4,sK7),sK5) | spl9_7),
% 0.21/0.56    inference(avatar_component_clause,[],[f296])).
% 0.21/0.56  fof(f330,plain,(
% 0.21/0.56    ~spl9_6),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f329])).
% 0.21/0.56  fof(f329,plain,(
% 0.21/0.56    $false | ~spl9_6),
% 0.21/0.56    inference(subsumption_resolution,[],[f323,f142])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ~v5_relat_1(sK7,k1_xboole_0)),
% 0.21/0.56    inference(subsumption_resolution,[],[f141,f105])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    ~v5_relat_1(sK7,k1_xboole_0) | ~v1_relat_1(sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f139,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    ~r1_tarski(k1_xboole_0,sK4) | ~v5_relat_1(sK7,k1_xboole_0) | ~v1_relat_1(sK7)),
% 0.21/0.56    inference(superposition,[],[f137,f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.56    inference(resolution,[],[f110,f69])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(resolution,[],[f74,f66])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(flattening,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    v5_relat_1(sK7,k1_xboole_0) | ~spl9_6),
% 0.21/0.56    inference(backward_demodulation,[],[f118,f317])).
% 0.21/0.56  fof(f317,plain,(
% 0.21/0.56    k1_xboole_0 = sK6 | ~spl9_6),
% 0.21/0.56    inference(resolution,[],[f226,f84])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    sP0(sK5,sK6) | ~spl9_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f224])).
% 0.21/0.56  fof(f224,plain,(
% 0.21/0.56    spl9_6 <=> sP0(sK5,sK6)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    v5_relat_1(sK7,sK6)),
% 0.21/0.56    inference(resolution,[],[f79,f63])).
% 0.21/0.56  fof(f304,plain,(
% 0.21/0.56    spl9_8 | ~spl9_7 | ~spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f290,f220,f296,f300])).
% 0.21/0.56  fof(f290,plain,(
% 0.21/0.56    ~m1_subset_1(sK8(sK5,sK4,sK7),sK5) | sP3(sK4,sK5,sK7) | ~spl9_5),
% 0.21/0.56    inference(resolution,[],[f288,f234])).
% 0.21/0.56  fof(f234,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0) | sP3(X0,sK5,sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f233,f105])).
% 0.21/0.56  fof(f233,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0) | sP3(X0,sK5,sK7) | ~v1_relat_1(sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f232,f61])).
% 0.21/0.56  fof(f232,plain,(
% 0.21/0.56    ( ! [X0] : (~r2_hidden(k1_funct_1(sK7,sK8(sK5,X0,sK7)),X0) | sP3(X0,sK5,sK7) | ~v1_funct_1(sK7) | ~v1_relat_1(sK7)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f103,f222])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK8(k1_relat_1(X2),X1,X2)),X1) | sP3(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK8(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f58])).
% 0.21/0.56  fof(f288,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f287,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ~v1_xboole_0(sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f287,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | v1_xboole_0(sK5)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f286,f61])).
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f285,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    v1_funct_2(sK7,sK5,sK6)),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f284,f63])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f283])).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(k1_funct_1(sK7,X0),sK4) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(X0,sK5) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) | ~v1_funct_2(sK7,sK5,sK6) | ~v1_funct_1(sK7) | v1_xboole_0(sK5)) )),
% 0.21/0.56    inference(superposition,[],[f64,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X4] : (r2_hidden(k3_funct_2(sK5,sK6,sK7,X4),sK4) | ~m1_subset_1(X4,sK5)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f227,plain,(
% 0.21/0.56    spl9_5 | spl9_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f218,f224,f220])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.21/0.56    inference(subsumption_resolution,[],[f214,f62])).
% 0.21/0.56  fof(f214,plain,(
% 0.21/0.56    ~v1_funct_2(sK7,sK5,sK6) | sP0(sK5,sK6) | sK5 = k1_relat_1(sK7)),
% 0.21/0.56    inference(resolution,[],[f185,f63])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f183,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(definition_folding,[],[f28,f39,f38,f37])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.56  fof(f183,plain,(
% 0.21/0.56    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.56    inference(superposition,[],[f82,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f38])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (10584)------------------------------
% 0.21/0.56  % (10584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10584)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (10584)Memory used [KB]: 6268
% 0.21/0.56  % (10584)Time elapsed: 0.120 s
% 0.21/0.56  % (10584)------------------------------
% 0.21/0.56  % (10584)------------------------------
% 0.21/0.56  % (10580)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (10588)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.56  % (10579)Success in time 0.196 s
%------------------------------------------------------------------------------
