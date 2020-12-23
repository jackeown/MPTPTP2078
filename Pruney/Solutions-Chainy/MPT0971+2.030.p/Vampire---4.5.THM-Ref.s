%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 192 expanded)
%              Number of leaves         :   26 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  367 ( 846 expanded)
%              Number of equality atoms :   91 ( 191 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f269,f320,f324,f621,f646,f670,f671,f728,f1077,f1289])).

fof(f1289,plain,
    ( ~ spl8_9
    | ~ spl8_48 ),
    inference(avatar_contradiction_clause,[],[f1280])).

fof(f1280,plain,
    ( $false
    | ~ spl8_9
    | ~ spl8_48 ),
    inference(unit_resulting_resolution,[],[f60,f1194])).

fof(f1194,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl8_9
    | ~ spl8_48 ),
    inference(backward_demodulation,[],[f868,f115])).

fof(f115,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f868,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl8_48 ),
    inference(resolution,[],[f850,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK7(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f850,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl8_48 ),
    inference(resolution,[],[f849,f727])).

fof(f727,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f725])).

fof(f725,plain,
    ( spl8_48
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f849,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0))
      | r2_hidden(sK2,X0) ) ),
    inference(forward_demodulation,[],[f158,f122])).

fof(f122,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f39,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f39,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ! [X4] :
        ( sK2 != k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f24])).

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
          ( sK2 != k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(sK2,X0)
      | ~ m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f40,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f40,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1077,plain,
    ( ~ spl8_24
    | ~ spl8_25
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f1074])).

fof(f1074,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_25
    | ~ spl8_29 ),
    inference(unit_resulting_resolution,[],[f764,f297,f41])).

fof(f41,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | sK2 != k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f297,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl8_25
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f764,plain,
    ( r2_hidden(sK6(sK3,sK2),sK0)
    | ~ spl8_24
    | ~ spl8_29 ),
    inference(forward_demodulation,[],[f292,f318])).

fof(f318,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl8_29
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f292,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_24
  <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f728,plain,
    ( ~ spl8_8
    | spl8_48 ),
    inference(avatar_split_clause,[],[f723,f725,f109])).

fof(f109,plain,
    ( spl8_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f723,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f49,f122])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f671,plain,
    ( ~ spl8_1
    | ~ spl8_13
    | spl8_25
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f664,f161,f295,f148,f79])).

fof(f79,plain,
    ( spl8_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f148,plain,
    ( spl8_13
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f161,plain,
    ( spl8_14
  <=> r2_hidden(sK2,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f664,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f163,f65])).

fof(f65,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK6(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK4(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X5)) = X5
        & r2_hidden(sK6(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

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

fof(f163,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f670,plain,
    ( ~ spl8_1
    | ~ spl8_13
    | spl8_24
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f663,f161,f290,f148,f79])).

fof(f663,plain,
    ( r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_14 ),
    inference(resolution,[],[f163,f66])).

fof(f66,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK6(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f646,plain,
    ( ~ spl8_8
    | spl8_14 ),
    inference(avatar_split_clause,[],[f645,f161,f109])).

fof(f645,plain,
    ( r2_hidden(sK2,k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f40,f57])).

fof(f621,plain,
    ( ~ spl8_8
    | spl8_9
    | spl8_10 ),
    inference(avatar_split_clause,[],[f620,f117,f113,f109])).

fof(f117,plain,
    ( spl8_10
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f620,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f38,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f38,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f324,plain,(
    spl8_13 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f37,f150])).

fof(f150,plain,
    ( ~ v1_funct_1(sK3)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f37,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f320,plain,
    ( ~ spl8_8
    | spl8_29
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f312,f117,f316,f109])).

fof(f312,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_10 ),
    inference(superposition,[],[f56,f119])).

fof(f119,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f269,plain,(
    spl8_8 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | spl8_8 ),
    inference(unit_resulting_resolution,[],[f39,f111])).

fof(f111,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl8_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f129,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f81,f58,f39,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f81,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (17881)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (17881)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f1290,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f129,f269,f320,f324,f621,f646,f670,f671,f728,f1077,f1289])).
% 0.20/0.47  fof(f1289,plain,(
% 0.20/0.47    ~spl8_9 | ~spl8_48),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f1280])).
% 0.20/0.47  fof(f1280,plain,(
% 0.20/0.47    $false | (~spl8_9 | ~spl8_48)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f60,f1194])).
% 0.20/0.47  fof(f1194,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | (~spl8_9 | ~spl8_48)),
% 0.20/0.47    inference(backward_demodulation,[],[f868,f115])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    k1_xboole_0 = sK1 | ~spl8_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f113])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    spl8_9 <=> k1_xboole_0 = sK1),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.47  fof(f868,plain,(
% 0.20/0.47    ~v1_xboole_0(sK1) | ~spl8_48),
% 0.20/0.47    inference(resolution,[],[f850,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK7(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f34,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK7(X0),X0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(rectify,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.47    inference(nnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.47  fof(f850,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1) | ~spl8_48),
% 0.20/0.47    inference(resolution,[],[f849,f727])).
% 0.20/0.47  fof(f727,plain,(
% 0.20/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl8_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f725])).
% 0.20/0.47  fof(f725,plain,(
% 0.20/0.47    spl8_48 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.20/0.47  fof(f849,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(X0)) | r2_hidden(sK2,X0)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f158,f122])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f39,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2,X0) | ~m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(resolution,[],[f40,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f1077,plain,(
% 0.20/0.47    ~spl8_24 | ~spl8_25 | ~spl8_29),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f1074])).
% 0.20/0.47  fof(f1074,plain,(
% 0.20/0.47    $false | (~spl8_24 | ~spl8_25 | ~spl8_29)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f764,f297,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X4] : (~r2_hidden(X4,sK0) | sK2 != k1_funct_1(sK3,X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f297,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~spl8_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f295])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    spl8_25 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 0.20/0.47  fof(f764,plain,(
% 0.20/0.47    r2_hidden(sK6(sK3,sK2),sK0) | (~spl8_24 | ~spl8_29)),
% 0.20/0.47    inference(forward_demodulation,[],[f292,f318])).
% 0.20/0.47  fof(f318,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~spl8_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f316])).
% 0.20/0.47  fof(f316,plain,(
% 0.20/0.47    spl8_29 <=> sK0 = k1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | ~spl8_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f290])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    spl8_24 <=> r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.20/0.47  fof(f728,plain,(
% 0.20/0.47    ~spl8_8 | spl8_48),
% 0.20/0.47    inference(avatar_split_clause,[],[f723,f725,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    spl8_8 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.47  fof(f723,plain,(
% 0.20/0.47    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(superposition,[],[f49,f122])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.47  fof(f671,plain,(
% 0.20/0.47    ~spl8_1 | ~spl8_13 | spl8_25 | ~spl8_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f664,f161,f295,f148,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    spl8_1 <=> v1_relat_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    spl8_13 <=> v1_funct_1(sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl8_14 <=> r2_hidden(sK2,k2_relat_1(sK3))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 0.20/0.47  fof(f664,plain,(
% 0.20/0.47    sK2 = k1_funct_1(sK3,sK6(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_14),
% 0.20/0.47    inference(resolution,[],[f163,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0,X5] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK6(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & ((sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f27,f30,f29,f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK4(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK4(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK4(X0,X1) = k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK6(X0,X5)) = X5 & r2_hidden(sK6(X0,X5),k1_relat_1(X0))))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(rectify,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(nnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | ~spl8_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f670,plain,(
% 0.20/0.47    ~spl8_1 | ~spl8_13 | spl8_24 | ~spl8_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f663,f161,f290,f148,f79])).
% 0.20/0.47  fof(f663,plain,(
% 0.20/0.47    r2_hidden(sK6(sK3,sK2),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl8_14),
% 0.20/0.47    inference(resolution,[],[f163,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X5] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f42])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X5,X1] : (r2_hidden(sK6(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f646,plain,(
% 0.20/0.47    ~spl8_8 | spl8_14),
% 0.20/0.47    inference(avatar_split_clause,[],[f645,f161,f109])).
% 0.20/0.47  fof(f645,plain,(
% 0.20/0.47    r2_hidden(sK2,k2_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(superposition,[],[f40,f57])).
% 0.20/0.47  fof(f621,plain,(
% 0.20/0.47    ~spl8_8 | spl8_9 | spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f620,f117,f113,f109])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    spl8_10 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.47  fof(f620,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(resolution,[],[f38,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(nnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    spl8_13),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f321])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    $false | spl8_13),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f37,f150])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ~v1_funct_1(sK3) | spl8_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f148])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    ~spl8_8 | spl8_29 | ~spl8_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f312,f117,f316,f109])).
% 0.20/0.47  fof(f312,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_10),
% 0.20/0.47    inference(superposition,[],[f56,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl8_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f117])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    spl8_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    $false | spl8_8),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f39,f111])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl8_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f109])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    spl8_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    $false | spl8_1),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f81,f58,f39,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    ~v1_relat_1(sK3) | spl8_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f79])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (17881)------------------------------
% 0.20/0.47  % (17881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (17881)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (17881)Memory used [KB]: 6780
% 0.20/0.47  % (17881)Time elapsed: 0.030 s
% 0.20/0.47  % (17881)------------------------------
% 0.20/0.47  % (17881)------------------------------
% 0.20/0.47  % (17867)Success in time 0.113 s
%------------------------------------------------------------------------------
