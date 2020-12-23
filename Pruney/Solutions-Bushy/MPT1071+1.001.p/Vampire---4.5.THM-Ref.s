%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1071+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:12 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  152 (4837 expanded)
%              Number of leaves         :   26 (1679 expanded)
%              Depth                    :   28
%              Number of atoms          :  648 (41750 expanded)
%              Number of equality atoms :  150 (7883 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f2028,f2116])).

fof(f2116,plain,
    ( spl12_1
    | ~ spl12_3 ),
    inference(avatar_contradiction_clause,[],[f2115])).

fof(f2115,plain,
    ( $false
    | spl12_1
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2108,f2088])).

fof(f2088,plain,
    ( sK3 != k1_funct_1(sK2,sK6(sK2))
    | spl12_1
    | ~ spl12_3 ),
    inference(backward_demodulation,[],[f2030,f2082])).

fof(f2082,plain,
    ( sK3 = k1_funct_1(sK2,sK5(sK2))
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f2064,f106])).

fof(f106,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2064,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(sK2)),k1_tarski(sK3))
    | spl12_1
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f2061,f2036])).

fof(f2036,plain,
    ( k1_tarski(sK3) = k2_relat_1(sK2)
    | ~ spl12_3 ),
    inference(backward_demodulation,[],[f164,f124])).

fof(f124,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl12_3
  <=> k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f164,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f72,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f72,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ! [X3] :
          ( k1_tarski(X3) != k2_relset_1(sK0,sK1,sK2)
          | ~ m1_subset_1(X3,sK1) )
      | ~ v3_funct_1(sK2) )
    & ( ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
        & m1_subset_1(sK3,sK1) )
      | v3_funct_1(sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f42,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ! [X3] :
                      ( k2_relset_1(X0,X1,X2) != k1_tarski(X3)
                      | ~ m1_subset_1(X3,X1) )
                  | ~ v3_funct_1(X2) )
                & ( ? [X4] :
                      ( k2_relset_1(X0,X1,X2) = k1_tarski(X4)
                      & m1_subset_1(X4,X1) )
                  | v3_funct_1(X2) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k1_tarski(X3) != k2_relset_1(sK0,X1,X2)
                    | ~ m1_subset_1(X3,X1) )
                | ~ v3_funct_1(X2) )
              & ( ? [X4] :
                    ( k1_tarski(X4) = k2_relset_1(sK0,X1,X2)
                    & m1_subset_1(X4,X1) )
                | v3_funct_1(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
              & v1_funct_2(X2,sK0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ! [X3] :
                  ( k1_tarski(X3) != k2_relset_1(sK0,X1,X2)
                  | ~ m1_subset_1(X3,X1) )
              | ~ v3_funct_1(X2) )
            & ( ? [X4] :
                  ( k1_tarski(X4) = k2_relset_1(sK0,X1,X2)
                  & m1_subset_1(X4,X1) )
              | v3_funct_1(X2) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
            & v1_funct_2(X2,sK0,X1)
            & v1_funct_1(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ( ! [X3] :
                ( k1_tarski(X3) != k2_relset_1(sK0,sK1,X2)
                | ~ m1_subset_1(X3,sK1) )
            | ~ v3_funct_1(X2) )
          & ( ? [X4] :
                ( k1_tarski(X4) = k2_relset_1(sK0,sK1,X2)
                & m1_subset_1(X4,sK1) )
            | v3_funct_1(X2) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X2,sK0,sK1)
          & v1_funct_1(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ( ! [X3] :
              ( k1_tarski(X3) != k2_relset_1(sK0,sK1,X2)
              | ~ m1_subset_1(X3,sK1) )
          | ~ v3_funct_1(X2) )
        & ( ? [X4] :
              ( k1_tarski(X4) = k2_relset_1(sK0,sK1,X2)
              & m1_subset_1(X4,sK1) )
          | v3_funct_1(X2) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X2,sK0,sK1)
        & v1_funct_1(X2) )
   => ( ( ! [X3] :
            ( k1_tarski(X3) != k2_relset_1(sK0,sK1,sK2)
            | ~ m1_subset_1(X3,sK1) )
        | ~ v3_funct_1(sK2) )
      & ( ? [X4] :
            ( k1_tarski(X4) = k2_relset_1(sK0,sK1,sK2)
            & m1_subset_1(X4,sK1) )
        | v3_funct_1(sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X4] :
        ( k1_tarski(X4) = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X4,sK1) )
   => ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
      & m1_subset_1(sK3,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k2_relset_1(X0,X1,X2) != k1_tarski(X3)
                    | ~ m1_subset_1(X3,X1) )
                | ~ v3_funct_1(X2) )
              & ( ? [X4] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X4)
                    & m1_subset_1(X4,X1) )
                | v3_funct_1(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k2_relset_1(X0,X1,X2) != k1_tarski(X3)
                    | ~ m1_subset_1(X3,X1) )
                | ~ v3_funct_1(X2) )
              & ( ? [X3] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                    & m1_subset_1(X3,X1) )
                | v3_funct_1(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ! [X3] :
                    ( k2_relset_1(X0,X1,X2) != k1_tarski(X3)
                    | ~ m1_subset_1(X3,X1) )
                | ~ v3_funct_1(X2) )
              & ( ? [X3] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                    & m1_subset_1(X3,X1) )
                | v3_funct_1(X2) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_funct_1(X2)
              <~> ? [X3] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                    & m1_subset_1(X3,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_funct_1(X2)
              <~> ? [X3] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                    & m1_subset_1(X3,X1) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X2,X0,X1)
                  & v1_funct_1(X2) )
               => ( v3_funct_1(X2)
                <=> ? [X3] :
                      ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                      & m1_subset_1(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ( v3_funct_1(X2)
              <=> ? [X3] :
                    ( k2_relset_1(X0,X1,X2) = k1_tarski(X3)
                    & m1_subset_1(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t188_funct_2)).

fof(f2061,plain,
    ( r2_hidden(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f2032,f108])).

fof(f108,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK9(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK9(X0,X1),X1) )
              & ( ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
                  & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK9(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK11(X0,X5)) = X5
                    & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f63,f66,f65,f64])).

fof(f64,plain,(
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
              ( k1_funct_1(X0,X3) != sK9(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK9(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK9(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
        & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK11(X0,X5)) = X5
        & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f2032,plain,
    ( r2_hidden(sK5(sK2),k1_relat_1(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f114,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v3_funct_1(X0)
          | ( k1_funct_1(X0,sK5(X0)) != k1_funct_1(X0,sK6(X0))
            & r2_hidden(sK6(X0),k1_relat_1(X0))
            & r2_hidden(sK5(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v3_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0)) != k1_funct_1(X0,sK6(X0))
        & r2_hidden(sK6(X0),k1_relat_1(X0))
        & r2_hidden(sK5(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v3_funct_1(X0)
          | ? [X1,X2] :
              ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( k1_funct_1(X0,X3) = k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v3_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v3_funct_1(X0)
          | ? [X1,X2] :
              ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v3_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => k1_funct_1(X0,X1) = k1_funct_1(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_funct_1)).

fof(f114,plain,
    ( ~ v3_funct_1(sK2)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl12_1
  <=> v3_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f70,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f152,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f72,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2030,plain,
    ( k1_funct_1(sK2,sK5(sK2)) != k1_funct_1(sK2,sK6(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f114,f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK5(X0)) != k1_funct_1(X0,sK6(X0))
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2108,plain,
    ( sK3 = k1_funct_1(sK2,sK6(sK2))
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f2071,f106])).

fof(f2071,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK2)),k1_tarski(sK3))
    | spl12_1
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f2031,f2058])).

fof(f2058,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK3))
        | ~ r2_hidden(X1,k1_relat_1(sK2)) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2057,f152])).

fof(f2057,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK3))
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2048,f70])).

fof(f2048,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK2,X1),k1_tarski(sK3))
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_3 ),
    inference(superposition,[],[f108,f2036])).

fof(f2031,plain,
    ( r2_hidden(sK6(sK2),k1_relat_1(sK2))
    | spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f114,f83])).

fof(f83,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),k1_relat_1(X0))
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2028,plain,(
    ~ spl12_1 ),
    inference(avatar_contradiction_clause,[],[f2027])).

fof(f2027,plain,
    ( $false
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f2026,f1399])).

fof(f1399,plain,
    ( sK7(k2_relat_1(sK2)) != sK9(sK2,k1_tarski(sK7(k2_relat_1(sK2))))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f315,f105,f1387])).

fof(f1387,plain,
    ( ! [X0] :
        ( sK9(sK2,X0) != sK7(k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK7(k2_relat_1(sK2)),X0) )
    | ~ spl12_1 ),
    inference(inner_rewriting,[],[f1367])).

fof(f1367,plain,
    ( ! [X0] :
        ( sK9(sK2,X0) != sK7(k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(sK2,X0),X0) )
    | ~ spl12_1 ),
    inference(backward_demodulation,[],[f410,f1358])).

fof(f1358,plain,
    ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) = sK7(k2_relat_1(sK2))
    | ~ spl12_1 ),
    inference(forward_demodulation,[],[f411,f308])).

fof(f308,plain,(
    sK7(k2_relat_1(sK2)) = k1_funct_1(sK2,sK11(sK2,sK7(k2_relat_1(sK2)))) ),
    inference(unit_resulting_resolution,[],[f152,f70,f306,f109])).

fof(f109,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f306,plain,(
    r2_hidden(sK7(k2_relat_1(sK2)),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f305,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f305,plain,(
    ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f217,f91])).

fof(f91,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f217,plain,(
    r2_hidden(k1_funct_1(sK2,sK7(k1_relat_1(sK2))),k2_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f152,f70,f186,f108])).

fof(f186,plain,(
    r2_hidden(sK7(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f85,f184,f90])).

fof(f184,plain,(
    ~ v1_xboole_0(k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f152,f182,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f182,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f68,f69,f70,f71,f72,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f71,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f69,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f10,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f411,plain,
    ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) = k1_funct_1(sK2,sK11(sK2,sK7(k2_relat_1(sK2))))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f115,f186,f309,f81])).

fof(f81,plain,(
    ! [X4,X0,X3] :
      ( ~ r2_hidden(X4,k1_relat_1(X0))
      | k1_funct_1(X0,X3) = k1_funct_1(X0,X4)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f309,plain,(
    r2_hidden(sK11(sK2,sK7(k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f152,f70,f306,f110])).

fof(f110,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f115,plain,
    ( v3_funct_1(sK2)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f410,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) != sK9(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(sK2,X0),X0) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f409,f152])).

fof(f409,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) != sK9(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(sK2,X0),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f408,f70])).

fof(f408,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) != sK9(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f406,f187])).

fof(f187,plain,(
    r2_hidden(sK8(k1_relat_1(sK2)),k1_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f184,f92])).

fof(f92,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f406,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) != sK9(sK2,X0)
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK8(k1_relat_1(sK2)),k1_relat_1(sK2))
        | ~ r2_hidden(sK9(sK2,X0),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl12_1 ),
    inference(superposition,[],[f100,f221])).

fof(f221,plain,
    ( k1_funct_1(sK2,sK7(k1_relat_1(sK2))) = k1_funct_1(sK2,sK8(k1_relat_1(sK2)))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f115,f186,f187,f81])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK9(X0,X1)
      | k2_relat_1(X0) = X1
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK9(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f105,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f315,plain,
    ( k2_relat_1(sK2) != k1_tarski(sK7(k2_relat_1(sK2)))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f310,f166])).

fof(f166,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != k2_relat_1(sK2)
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl12_1 ),
    inference(backward_demodulation,[],[f126,f164])).

fof(f126,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != k2_relset_1(sK0,sK1,sK2)
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl12_1 ),
    inference(subsumption_resolution,[],[f75,f115])).

fof(f75,plain,(
    ! [X3] :
      ( k1_tarski(X3) != k2_relset_1(sK0,sK1,sK2)
      | ~ m1_subset_1(X3,sK1)
      | ~ v3_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f310,plain,(
    m1_subset_1(sK7(k2_relat_1(sK2)),sK1) ),
    inference(unit_resulting_resolution,[],[f171,f306,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f171,plain,(
    m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f162,f164])).

fof(f162,plain,(
    m1_subset_1(k2_relset_1(sK0,sK1,sK2),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f72,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f2026,plain,
    ( sK7(k2_relat_1(sK2)) = sK9(sK2,k1_tarski(sK7(k2_relat_1(sK2))))
    | ~ spl12_1 ),
    inference(forward_demodulation,[],[f1402,f1423])).

fof(f1423,plain,
    ( sK7(k2_relat_1(sK2)) = k1_funct_1(sK2,sK10(sK2,k1_tarski(sK7(k2_relat_1(sK2)))))
    | ~ spl12_1 ),
    inference(forward_demodulation,[],[f1417,f308])).

fof(f1417,plain,
    ( k1_funct_1(sK2,sK11(sK2,sK7(k2_relat_1(sK2)))) = k1_funct_1(sK2,sK10(sK2,k1_tarski(sK7(k2_relat_1(sK2)))))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f115,f309,f1403,f81])).

fof(f1403,plain,
    ( r2_hidden(sK10(sK2,k1_tarski(sK7(k2_relat_1(sK2)))),k1_relat_1(sK2))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f315,f1400,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK9(X0,X1),X1)
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1400,plain,
    ( ~ r2_hidden(sK9(sK2,k1_tarski(sK7(k2_relat_1(sK2)))),k1_tarski(sK7(k2_relat_1(sK2))))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f1399,f106])).

fof(f1402,plain,
    ( sK9(sK2,k1_tarski(sK7(k2_relat_1(sK2)))) = k1_funct_1(sK2,sK10(sK2,k1_tarski(sK7(k2_relat_1(sK2)))))
    | ~ spl12_1 ),
    inference(unit_resulting_resolution,[],[f152,f70,f315,f1400,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
      | k2_relat_1(X0) = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f125,plain,
    ( spl12_1
    | spl12_3 ),
    inference(avatar_split_clause,[],[f74,f122,f113])).

fof(f74,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
    | v3_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

%------------------------------------------------------------------------------
