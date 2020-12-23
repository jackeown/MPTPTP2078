%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 949 expanded)
%              Number of leaves         :   22 ( 298 expanded)
%              Depth                    :   30
%              Number of atoms          :  580 (5658 expanded)
%              Number of equality atoms :  161 (1656 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f120,f200,f427,f457])).

fof(f457,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(avatar_contradiction_clause,[],[f456])).

fof(f456,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(subsumption_resolution,[],[f438,f87])).

fof(f87,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f438,plain,
    ( r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_8 ),
    inference(backward_demodulation,[],[f245,f179])).

fof(f179,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f245,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f244,f95])).

fof(f95,plain,(
    sK1 != k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f94,f45])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    & ! [X3] :
        ( ( k1_funct_1(sK2,sK3(X3)) = X3
          & r2_hidden(sK3(X3),sK0) )
        | ~ r2_hidden(X3,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27,f26])).

fof(f26,plain,
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

fof(f27,plain,(
    ! [X3] :
      ( ? [X4] :
          ( k1_funct_1(sK2,X4) = X3
          & r2_hidden(X4,sK0) )
     => ( k1_funct_1(sK2,sK3(X3)) = X3
        & r2_hidden(sK3(X3),sK0) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f94,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f48,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f48,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f244,plain,
    ( r2_hidden(sK4(sK2,sK1),sK1)
    | sK1 = k2_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(factoring,[],[f238])).

fof(f238,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK2,X1),sK1)
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK4(sK2,X1),X1) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( ! [X1] :
        ( r2_hidden(sK4(sK2,X1),sK1)
        | k2_relat_1(sK2) = X1
        | r2_hidden(sK4(sK2,X1),X1)
        | r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1 )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f154,f231])).

fof(f231,plain,
    ( ! [X0] :
        ( sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f230,f111])).

fof(f111,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl8_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f230,plain,(
    ! [X0] :
      ( sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0))
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f54,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).

fof(f31,plain,(
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

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f154,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),sK1)
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f145,f45])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f144,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK2,X1)
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1)
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f142,f111])).

fof(f142,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1)
        | r2_hidden(sK4(sK2,X0),X0)
        | ~ v5_relat_1(sK2,X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f128,plain,
    ( ! [X2,X3] :
        ( ~ r1_tarski(k2_relat_1(sK2),X3)
        | k2_relat_1(sK2) = X2
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X2)),X3)
        | r2_hidden(sK4(sK2,X2),X2) )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f124,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f124,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | r2_hidden(sK4(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f123,f111])).

fof(f123,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f121,f43])).

fof(f121,plain,
    ( ! [X0] :
        ( k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0)
        | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f115,f77])).

fof(f77,plain,(
    ! [X6,X0] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) )
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl8_4
  <=> ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | r2_hidden(sK4(sK2,X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f427,plain,
    ( ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f420,f268])).

fof(f268,plain,
    ( r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f267,f206])).

fof(f206,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f204,f45])).

fof(f204,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_9 ),
    inference(superposition,[],[f183,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f183,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl8_9
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f267,plain,
    ( r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f266,f111])).

fof(f266,plain,
    ( r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f262,f43])).

fof(f262,plain,
    ( r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f260,f79])).

fof(f79,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f260,plain,
    ( r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(backward_demodulation,[],[f246,f248])).

fof(f248,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1)))
    | ~ spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f245,f47])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | k1_funct_1(sK2,sK3(X3)) = X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,
    ( r2_hidden(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),k2_relat_1(sK2))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f245,f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK2,sK3(X0)),k2_relat_1(sK2)) )
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(resolution,[],[f215,f46])).

fof(f46,plain,(
    ! [X3] :
      ( r2_hidden(sK3(X3),sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) )
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f214,f111])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f213,f43])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl8_9 ),
    inference(superposition,[],[f77,f206])).

fof(f420,plain,
    ( ~ r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(trivial_inequality_removal,[],[f419])).

fof(f419,plain,
    ( sK4(sK2,sK1) != sK4(sK2,sK1)
    | ~ r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(superposition,[],[f415,f265])).

fof(f265,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1)))
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f264,f111])).

fof(f264,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f261,f43])).

fof(f261,plain,
    ( sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f260,f78])).

fof(f78,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f415,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(subsumption_resolution,[],[f410,f95])).

fof(f410,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,X0) != sK4(sK2,sK1)
        | ~ r2_hidden(X0,sK0)
        | sK1 = k2_relat_1(sK2) )
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_9 ),
    inference(resolution,[],[f318,f245])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK2,X1),X1)
        | sK4(sK2,X1) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,sK0)
        | k2_relat_1(sK2) = X1 )
    | ~ spl8_3
    | ~ spl8_9 ),
    inference(forward_demodulation,[],[f317,f206])).

fof(f317,plain,
    ( ! [X0,X1] :
        ( sK4(sK2,X1) != k1_funct_1(sK2,X0)
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK4(sK2,X1),X1)
        | k2_relat_1(sK2) = X1 )
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f316,f111])).

fof(f316,plain,(
    ! [X0,X1] :
      ( sK4(sK2,X1) != k1_funct_1(sK2,X0)
      | ~ r2_hidden(X0,k1_relat_1(sK2))
      | ~ r2_hidden(sK4(sK2,X1),X1)
      | k2_relat_1(sK2) = X1
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | k1_funct_1(X0,X3) != sK4(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f200,plain,
    ( spl8_9
    | spl8_8 ),
    inference(avatar_split_clause,[],[f199,f177,f181])).

fof(f199,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(global_subsumption,[],[f175])).

fof(f175,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f174,f45])).

fof(f174,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f120,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl8_3 ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f56,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl8_3 ),
    inference(resolution,[],[f117,f45])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl8_3 ),
    inference(resolution,[],[f112,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f112,plain,
    ( ~ v1_relat_1(sK2)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f116,plain,
    ( ~ spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f108,f114,f110])).

fof(f108,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK4(sK2,X0),X0)
      | k2_relat_1(sK2) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f53,f43])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK4(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.50  % (2912)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (2919)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.51  % (2891)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (2896)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (2899)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (2906)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (2915)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (2893)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2913)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (2898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (2914)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (2894)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (2903)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (2904)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (2918)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (2901)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (2908)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (2902)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (2902)Refutation not found, incomplete strategy% (2902)------------------------------
% 0.20/0.54  % (2902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2902)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2902)Memory used [KB]: 10746
% 0.20/0.54  % (2902)Time elapsed: 0.132 s
% 0.20/0.54  % (2902)------------------------------
% 0.20/0.54  % (2902)------------------------------
% 0.20/0.54  % (2892)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (2901)Refutation not found, incomplete strategy% (2901)------------------------------
% 0.20/0.54  % (2901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2897)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (2908)Refutation not found, incomplete strategy% (2908)------------------------------
% 0.20/0.54  % (2908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2907)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (2909)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (2910)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (2917)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (2901)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2901)Memory used [KB]: 10746
% 0.20/0.55  % (2901)Time elapsed: 0.137 s
% 0.20/0.55  % (2901)------------------------------
% 0.20/0.55  % (2901)------------------------------
% 0.20/0.55  % (2908)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (2908)Memory used [KB]: 10746
% 0.20/0.55  % (2908)Time elapsed: 0.144 s
% 0.20/0.55  % (2908)------------------------------
% 0.20/0.55  % (2908)------------------------------
% 0.20/0.55  % (2900)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (2920)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.56  % (2916)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.56  % (2921)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.56  % (2905)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.57  % (2894)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % SZS output start Proof for theBenchmark
% 0.20/0.57  fof(f470,plain,(
% 0.20/0.57    $false),
% 0.20/0.57    inference(avatar_sat_refutation,[],[f116,f120,f200,f427,f457])).
% 0.20/0.57  fof(f457,plain,(
% 0.20/0.57    ~spl8_3 | ~spl8_4 | ~spl8_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f456])).
% 0.20/0.57  fof(f456,plain,(
% 0.20/0.57    $false | (~spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.20/0.57    inference(subsumption_resolution,[],[f438,f87])).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(superposition,[],[f57,f80])).
% 0.20/0.57  fof(f80,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f65])).
% 0.20/0.57  fof(f65,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.20/0.57    inference(cnf_transformation,[],[f41])).
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.57    inference(flattening,[],[f40])).
% 0.20/0.57  fof(f40,plain,(
% 0.20/0.57    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.20/0.57    inference(nnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f3])).
% 0.20/0.57  fof(f3,axiom,(
% 0.20/0.57    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.57  fof(f438,plain,(
% 0.20/0.57    r2_hidden(sK4(sK2,k1_xboole_0),k1_xboole_0) | (~spl8_3 | ~spl8_4 | ~spl8_8)),
% 0.20/0.57    inference(backward_demodulation,[],[f245,f179])).
% 0.20/0.57  fof(f179,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | ~spl8_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f177])).
% 0.20/0.57  fof(f177,plain,(
% 0.20/0.57    spl8_8 <=> k1_xboole_0 = sK1),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.57  fof(f245,plain,(
% 0.20/0.57    r2_hidden(sK4(sK2,sK1),sK1) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f244,f95])).
% 0.20/0.57  fof(f95,plain,(
% 0.20/0.57    sK1 != k2_relat_1(sK2)),
% 0.20/0.57    inference(subsumption_resolution,[],[f94,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f28,plain,(
% 0.20/0.57    sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : ((k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f27,f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (sK1 != k2_relset_1(sK0,sK1,sK2) & ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) | ~r2_hidden(X3,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X3] : (? [X4] : (k1_funct_1(sK2,X4) = X3 & r2_hidden(X4,sK0)) => (k1_funct_1(sK2,sK3(X3)) = X3 & r2_hidden(sK3(X3),sK0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f15,plain,(
% 0.20/0.57    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.57    inference(flattening,[],[f14])).
% 0.20/0.57  fof(f14,plain,(
% 0.20/0.57    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,negated_conjecture,(
% 0.20/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.57    inference(negated_conjecture,[],[f12])).
% 0.20/0.57  fof(f12,conjecture,(
% 0.20/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.20/0.57  fof(f94,plain,(
% 0.20/0.57    sK1 != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(superposition,[],[f48,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.57  fof(f48,plain,(
% 0.20/0.57    sK1 != k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f244,plain,(
% 0.20/0.57    r2_hidden(sK4(sK2,sK1),sK1) | sK1 = k2_relat_1(sK2) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(factoring,[],[f238])).
% 0.20/0.57  fof(f238,plain,(
% 0.20/0.57    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK1) | k2_relat_1(sK2) = X1 | r2_hidden(sK4(sK2,X1),X1)) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(duplicate_literal_removal,[],[f233])).
% 0.20/0.57  fof(f233,plain,(
% 0.20/0.57    ( ! [X1] : (r2_hidden(sK4(sK2,X1),sK1) | k2_relat_1(sK2) = X1 | r2_hidden(sK4(sK2,X1),X1) | r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(superposition,[],[f154,f231])).
% 0.20/0.57  fof(f231,plain,(
% 0.20/0.57    ( ! [X0] : (sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | ~spl8_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f230,f111])).
% 0.20/0.57  fof(f111,plain,(
% 0.20/0.57    v1_relat_1(sK2) | ~spl8_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f110])).
% 0.20/0.57  fof(f110,plain,(
% 0.20/0.57    spl8_3 <=> v1_relat_1(sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.57  fof(f230,plain,(
% 0.20/0.57    ( ! [X0] : (sK4(sK2,X0) = k1_funct_1(sK2,sK5(sK2,X0)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) )),
% 0.20/0.57    inference(resolution,[],[f54,f43])).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    v1_funct_1(sK2)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f30,f33,f32,f31])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(rectify,[],[f29])).
% 0.20/0.57  fof(f29,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(nnf_transformation,[],[f18])).
% 0.20/0.57  fof(f18,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(flattening,[],[f17])).
% 0.20/0.57  fof(f17,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.57  fof(f154,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),sK1) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(resolution,[],[f145,f45])).
% 0.20/0.57  fof(f145,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1)) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(resolution,[],[f144,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.57  fof(f144,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v5_relat_1(sK2,X1) | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f142,f111])).
% 0.20/0.57  fof(f142,plain,(
% 0.20/0.57    ( ! [X0,X1] : (k2_relat_1(sK2) = X0 | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1) | r2_hidden(sK4(sK2,X0),X0) | ~v5_relat_1(sK2,X1) | ~v1_relat_1(sK2)) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(resolution,[],[f128,f58])).
% 0.20/0.57  fof(f58,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(nnf_transformation,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.57  fof(f128,plain,(
% 0.20/0.57    ( ! [X2,X3] : (~r1_tarski(k2_relat_1(sK2),X3) | k2_relat_1(sK2) = X2 | r2_hidden(k1_funct_1(sK2,sK5(sK2,X2)),X3) | r2_hidden(sK4(sK2,X2),X2)) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(resolution,[],[f124,f60])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f39])).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(rectify,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.57    inference(nnf_transformation,[],[f20])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.57    inference(ennf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.57  fof(f124,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0) ) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(subsumption_resolution,[],[f123,f111])).
% 0.20/0.57  fof(f123,plain,(
% 0.20/0.57    ( ! [X0] : (k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl8_4),
% 0.20/0.57    inference(subsumption_resolution,[],[f121,f43])).
% 0.20/0.57  fof(f121,plain,(
% 0.20/0.57    ( ! [X0] : (k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0) | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_4),
% 0.20/0.57    inference(resolution,[],[f115,f77])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X6,X0] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f76])).
% 0.20/0.57  fof(f76,plain,(
% 0.20/0.57    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f115,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0)) ) | ~spl8_4),
% 0.20/0.57    inference(avatar_component_clause,[],[f114])).
% 0.20/0.57  fof(f114,plain,(
% 0.20/0.57    spl8_4 <=> ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | k2_relat_1(sK2) = X0 | r2_hidden(sK4(sK2,X0),X0))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.57  fof(f427,plain,(
% 0.20/0.57    ~spl8_3 | ~spl8_4 | ~spl8_9),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f426])).
% 0.20/0.57  fof(f426,plain,(
% 0.20/0.57    $false | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f420,f268])).
% 0.20/0.57  fof(f268,plain,(
% 0.20/0.57    r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(forward_demodulation,[],[f267,f206])).
% 0.20/0.57  fof(f206,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK2) | ~spl8_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f204,f45])).
% 0.20/0.57  fof(f204,plain,(
% 0.20/0.57    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_9),
% 0.20/0.57    inference(superposition,[],[f183,f66])).
% 0.20/0.57  fof(f66,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.57  fof(f183,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl8_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f181])).
% 0.20/0.57  fof(f181,plain,(
% 0.20/0.57    spl8_9 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f266,f111])).
% 0.20/0.57  fof(f266,plain,(
% 0.20/0.57    r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f262,f43])).
% 0.20/0.57  fof(f262,plain,(
% 0.20/0.57    r2_hidden(sK6(sK2,sK4(sK2,sK1)),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(resolution,[],[f260,f79])).
% 0.20/0.57  fof(f79,plain,(
% 0.20/0.57    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f260,plain,(
% 0.20/0.57    r2_hidden(sK4(sK2,sK1),k2_relat_1(sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(backward_demodulation,[],[f246,f248])).
% 0.20/0.57  fof(f248,plain,(
% 0.20/0.57    sK4(sK2,sK1) = k1_funct_1(sK2,sK3(sK4(sK2,sK1))) | (~spl8_3 | ~spl8_4)),
% 0.20/0.57    inference(resolution,[],[f245,f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X3] : (~r2_hidden(X3,sK1) | k1_funct_1(sK2,sK3(X3)) = X3) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f246,plain,(
% 0.20/0.57    r2_hidden(k1_funct_1(sK2,sK3(sK4(sK2,sK1))),k2_relat_1(sK2)) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(resolution,[],[f245,f216])).
% 0.20/0.57  fof(f216,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK2,sK3(X0)),k2_relat_1(sK2))) ) | (~spl8_3 | ~spl8_9)),
% 0.20/0.57    inference(resolution,[],[f215,f46])).
% 0.20/0.57  fof(f46,plain,(
% 0.20/0.57    ( ! [X3] : (r2_hidden(sK3(X3),sK0) | ~r2_hidden(X3,sK1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))) ) | (~spl8_3 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f214,f111])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | ~spl8_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f213,f43])).
% 0.20/0.57  fof(f213,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl8_9),
% 0.20/0.57    inference(superposition,[],[f77,f206])).
% 0.20/0.57  fof(f420,plain,(
% 0.20/0.57    ~r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(trivial_inequality_removal,[],[f419])).
% 0.20/0.57  fof(f419,plain,(
% 0.20/0.57    sK4(sK2,sK1) != sK4(sK2,sK1) | ~r2_hidden(sK6(sK2,sK4(sK2,sK1)),sK0) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(superposition,[],[f415,f265])).
% 0.20/0.57  fof(f265,plain,(
% 0.20/0.57    sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1))) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f264,f111])).
% 0.20/0.57  fof(f264,plain,(
% 0.20/0.57    sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1))) | ~v1_relat_1(sK2) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f261,f43])).
% 0.20/0.57  fof(f261,plain,(
% 0.20/0.57    sK4(sK2,sK1) = k1_funct_1(sK2,sK6(sK2,sK4(sK2,sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(resolution,[],[f260,f78])).
% 0.20/0.57  fof(f78,plain,(
% 0.20/0.57    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | k1_funct_1(X0,sK6(X0,X5)) = X5 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(equality_resolution,[],[f51])).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f415,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(X0,sK0)) ) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(subsumption_resolution,[],[f410,f95])).
% 0.20/0.57  fof(f410,plain,(
% 0.20/0.57    ( ! [X0] : (k1_funct_1(sK2,X0) != sK4(sK2,sK1) | ~r2_hidden(X0,sK0) | sK1 = k2_relat_1(sK2)) ) | (~spl8_3 | ~spl8_4 | ~spl8_9)),
% 0.20/0.57    inference(resolution,[],[f318,f245])).
% 0.20/0.57  fof(f318,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(sK4(sK2,X1),X1) | sK4(sK2,X1) != k1_funct_1(sK2,X0) | ~r2_hidden(X0,sK0) | k2_relat_1(sK2) = X1) ) | (~spl8_3 | ~spl8_9)),
% 0.20/0.57    inference(forward_demodulation,[],[f317,f206])).
% 0.20/0.57  fof(f317,plain,(
% 0.20/0.57    ( ! [X0,X1] : (sK4(sK2,X1) != k1_funct_1(sK2,X0) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1) ) | ~spl8_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f316,f111])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    ( ! [X0,X1] : (sK4(sK2,X1) != k1_funct_1(sK2,X0) | ~r2_hidden(X0,k1_relat_1(sK2)) | ~r2_hidden(sK4(sK2,X1),X1) | k2_relat_1(sK2) = X1 | ~v1_relat_1(sK2)) )),
% 0.20/0.57    inference(resolution,[],[f55,f43])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    spl8_9 | spl8_8),
% 0.20/0.57    inference(avatar_split_clause,[],[f199,f177,f181])).
% 0.20/0.57  fof(f199,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.57    inference(global_subsumption,[],[f175])).
% 0.20/0.57  fof(f175,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 0.20/0.57    inference(subsumption_resolution,[],[f174,f45])).
% 0.20/0.57  fof(f174,plain,(
% 0.20/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.57    inference(resolution,[],[f70,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.57    inference(cnf_transformation,[],[f28])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(nnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(flattening,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.57  fof(f120,plain,(
% 0.20/0.57    spl8_3),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f119])).
% 0.20/0.57  fof(f119,plain,(
% 0.20/0.57    $false | spl8_3),
% 0.20/0.57    inference(subsumption_resolution,[],[f118,f56])).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  fof(f118,plain,(
% 0.20/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl8_3),
% 0.20/0.57    inference(resolution,[],[f117,f45])).
% 0.20/0.57  fof(f117,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl8_3),
% 0.20/0.57    inference(resolution,[],[f112,f49])).
% 0.20/0.57  fof(f49,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f16])).
% 0.20/0.57  fof(f16,plain,(
% 0.20/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.57  fof(f112,plain,(
% 0.20/0.57    ~v1_relat_1(sK2) | spl8_3),
% 0.20/0.57    inference(avatar_component_clause,[],[f110])).
% 0.20/0.57  fof(f116,plain,(
% 0.20/0.57    ~spl8_3 | spl8_4),
% 0.20/0.57    inference(avatar_split_clause,[],[f108,f114,f110])).
% 0.20/0.57  fof(f108,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) | r2_hidden(sK4(sK2,X0),X0) | k2_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) )),
% 0.20/0.57    inference(resolution,[],[f53,f43])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_funct_1(X0) | r2_hidden(sK5(X0,X1),k1_relat_1(X0)) | r2_hidden(sK4(X0,X1),X1) | k2_relat_1(X0) = X1 | ~v1_relat_1(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f34])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (2894)------------------------------
% 0.20/0.57  % (2894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (2894)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (2894)Memory used [KB]: 11001
% 0.20/0.57  % (2894)Time elapsed: 0.156 s
% 0.20/0.57  % (2894)------------------------------
% 0.20/0.57  % (2894)------------------------------
% 0.20/0.57  % (2890)Success in time 0.224 s
%------------------------------------------------------------------------------
