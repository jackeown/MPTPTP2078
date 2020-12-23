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
% DateTime   : Thu Dec  3 13:02:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 780 expanded)
%              Number of leaves         :   18 ( 204 expanded)
%              Depth                    :   25
%              Number of atoms          :  506 (4792 expanded)
%              Number of equality atoms :  127 (1318 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f382,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f149,f169,f372])).

fof(f372,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f370,f85])).

fof(f85,plain,(
    sP0(sK4,sK1) ),
    inference(subsumption_resolution,[],[f84,f38])).

fof(f38,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
    & k1_xboole_0 != sK2
    & r2_hidden(sK3,sK1)
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v2_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
      & k1_xboole_0 != sK2
      & r2_hidden(sK3,sK1)
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f84,plain,
    ( sP0(sK4,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f83,f39])).

fof(f39,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,
    ( sP0(sK4,sK1)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f76,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,
    ( k1_xboole_0 = sK2
    | sP0(sK4,sK1)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f40,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | sP0(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f20,f24])).

fof(f24,plain,(
    ! [X2,X0] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ~ sP0(X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_1(X2)
      <=> ! [X3,X4] :
            ( X3 = X4
            | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X3,X0) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => ( v2_funct_1(X2)
        <=> ! [X3,X4] :
              ( ( k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
                & r2_hidden(X4,X0)
                & r2_hidden(X3,X0) )
             => X3 = X4 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).

fof(f40,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f27])).

fof(f370,plain,
    ( ~ sP0(sK4,sK1)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f368,f42])).

fof(f42,plain,(
    r2_hidden(sK3,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f368,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ sP0(sK4,sK1)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(resolution,[],[f366,f185])).

fof(f185,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),sK1)
    | ~ spl10_1
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f108,f175])).

fof(f175,plain,
    ( k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK7(sK4,sK1,k1_funct_1(sK4,sK3))
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f174,f95])).

fof(f95,plain,(
    k1_funct_1(sK4,sK3) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3))) ),
    inference(resolution,[],[f94,f42])).

fof(f94,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0))) ) ),
    inference(subsumption_resolution,[],[f93,f86])).

fof(f86,plain,(
    v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f79,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f79,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f40,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f93,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0)))
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0)))
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,X0),k9_relat_1(sK4,sK1))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(forward_demodulation,[],[f82,f90])).

fof(f90,plain,(
    k2_relset_1(sK1,sK2,sK4) = k9_relat_1(sK4,sK1) ),
    inference(forward_demodulation,[],[f77,f75])).

fof(f75,plain,(
    ! [X1] : k7_relset_1(sK1,sK2,sK4,X1) = k9_relat_1(sK4,X1) ),
    inference(resolution,[],[f40,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

% (16357)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f77,plain,(
    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) ) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
      | ~ v1_funct_2(sK4,sK1,sK2)
      | ~ v1_funct_1(sK4) ) ),
    inference(subsumption_resolution,[],[f74,f43])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))
      | ~ v1_funct_2(sK4,sK1,sK2)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f40,f67])).

% (16354)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

fof(f174,plain,
    ( sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3))))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f173,f86])).

fof(f173,plain,
    ( sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3))))
    | ~ v1_relat_1(sK4)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f172,f38])).

fof(f172,plain,
    ( sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3))))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f170,f41])).

fof(f41,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f27])).

fof(f170,plain,
    ( sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3))))
    | ~ v2_funct_1(sK4)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl10_3 ),
    inference(resolution,[],[f121,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f121,plain,
    ( r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl10_3
  <=> r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f108,plain,
    ( r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl10_1
  <=> r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X0)
        | ~ r2_hidden(sK3,X0)
        | ~ sP0(sK4,X0) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f365,f44])).

fof(f44,plain,(
    sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f365,plain,
    ( ! [X0] :
        ( sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X0)
        | ~ r2_hidden(sK3,X0)
        | ~ sP0(sK4,X0) )
    | ~ spl10_3 ),
    inference(equality_resolution,[],[f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4,sK3) != k1_funct_1(sK4,X0)
        | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = X0
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X1)
        | ~ r2_hidden(X0,X1)
        | ~ sP0(sK4,X1) )
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f197,f41])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK4,sK3) != k1_funct_1(sK4,X0)
        | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = X0
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X1)
        | ~ r2_hidden(X0,X1)
        | ~ v2_funct_1(sK4)
        | ~ sP0(sK4,X1) )
    | ~ spl10_3 ),
    inference(superposition,[],[f59,f186])).

fof(f186,plain,
    ( k1_funct_1(sK4,sK3) = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)))
    | ~ spl10_3 ),
    inference(backward_demodulation,[],[f95,f175])).

fof(f59,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
      | X4 = X5
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ v2_funct_1(X0)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ( sK8(X0,X1) != sK9(X0,X1)
            & k1_funct_1(X0,sK8(X0,X1)) = k1_funct_1(X0,sK9(X0,X1))
            & r2_hidden(sK9(X0,X1),X1)
            & r2_hidden(sK8(X0,X1),X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK8(X0,X1) != sK9(X0,X1)
        & k1_funct_1(X0,sK8(X0,X1)) = k1_funct_1(X0,sK9(X0,X1))
        & r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_1(X0)
          | ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X0,X2) = k1_funct_1(X0,X3)
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1) ) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X0,X4) != k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          | ~ v2_funct_1(X0) ) )
      | ~ sP0(X0,X1) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( ( ( v2_funct_1(X2)
          | ? [X3,X4] :
              ( X3 != X4
              & k1_funct_1(X2,X3) = k1_funct_1(X2,X4)
              & r2_hidden(X4,X0)
              & r2_hidden(X3,X0) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X2,X3) != k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X3,X0) )
          | ~ v2_funct_1(X2) ) )
      | ~ sP0(X2,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f169,plain,
    ( ~ spl10_2
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f168])).

fof(f168,plain,
    ( $false
    | ~ spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f167,f86])).

fof(f167,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f166,f38])).

fof(f166,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f165,f113])).

fof(f113,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl10_2
  <=> r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f165,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl10_3 ),
    inference(resolution,[],[f122,f72])).

fof(f72,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f122,plain,
    ( ~ r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f149,plain,(
    spl10_1 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl10_1 ),
    inference(subsumption_resolution,[],[f146,f42])).

fof(f146,plain,
    ( ~ r2_hidden(sK3,sK1)
    | spl10_1 ),
    inference(resolution,[],[f145,f91])).

fof(f145,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f144,f86])).

fof(f144,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | ~ v1_relat_1(sK4)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f143,f38])).

fof(f143,plain,
    ( ~ r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | spl10_1 ),
    inference(resolution,[],[f109,f71])).

fof(f71,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,
    ( ~ r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f114,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f101,f111,f107])).

fof(f101,plain,
    ( r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))
    | ~ r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1) ),
    inference(superposition,[],[f91,f95])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (16347)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (16348)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (16350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (16347)Refutation not found, incomplete strategy% (16347)------------------------------
% 0.21/0.50  % (16347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16349)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (16348)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (16366)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (16363)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (16355)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (16347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (16347)Memory used [KB]: 10618
% 0.21/0.51  % (16347)Time elapsed: 0.085 s
% 0.21/0.51  % (16347)------------------------------
% 0.21/0.51  % (16347)------------------------------
% 0.21/0.51  % (16367)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (16352)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (16368)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (16370)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (16361)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (16358)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (16353)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (16358)Refutation not found, incomplete strategy% (16358)------------------------------
% 0.21/0.53  % (16358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (16358)Memory used [KB]: 10746
% 0.21/0.53  % (16358)Time elapsed: 0.110 s
% 0.21/0.53  % (16358)------------------------------
% 0.21/0.53  % (16358)------------------------------
% 1.30/0.53  % (16353)Refutation not found, incomplete strategy% (16353)------------------------------
% 1.30/0.53  % (16353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (16353)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (16353)Memory used [KB]: 10618
% 1.30/0.53  % (16353)Time elapsed: 0.116 s
% 1.30/0.53  % (16353)------------------------------
% 1.30/0.53  % (16353)------------------------------
% 1.30/0.53  % (16356)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.30/0.53  % (16369)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.30/0.53  % SZS output start Proof for theBenchmark
% 1.30/0.53  fof(f382,plain,(
% 1.30/0.53    $false),
% 1.30/0.53    inference(avatar_sat_refutation,[],[f114,f149,f169,f372])).
% 1.30/0.53  fof(f372,plain,(
% 1.30/0.53    ~spl10_1 | ~spl10_3),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f371])).
% 1.30/0.53  fof(f371,plain,(
% 1.30/0.53    $false | (~spl10_1 | ~spl10_3)),
% 1.30/0.53    inference(subsumption_resolution,[],[f370,f85])).
% 1.30/0.53  fof(f85,plain,(
% 1.30/0.53    sP0(sK4,sK1)),
% 1.30/0.53    inference(subsumption_resolution,[],[f84,f38])).
% 1.30/0.53  fof(f38,plain,(
% 1.30/0.53    v1_funct_1(sK4)),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f27,plain,(
% 1.30/0.53    sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f26])).
% 1.30/0.53  fof(f26,plain,(
% 1.30/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) & k1_xboole_0 != sK2 & r2_hidden(sK3,sK1) & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f12,plain,(
% 1.30/0.53    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.30/0.53    inference(flattening,[],[f11])).
% 1.30/0.53  fof(f11,plain,(
% 1.30/0.53    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.30/0.53    inference(ennf_transformation,[],[f10])).
% 1.30/0.53  fof(f10,negated_conjecture,(
% 1.30/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.30/0.53    inference(negated_conjecture,[],[f9])).
% 1.30/0.53  fof(f9,conjecture,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 1.30/0.53  fof(f84,plain,(
% 1.30/0.53    sP0(sK4,sK1) | ~v1_funct_1(sK4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f83,f39])).
% 1.30/0.53  fof(f39,plain,(
% 1.30/0.53    v1_funct_2(sK4,sK1,sK2)),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f83,plain,(
% 1.30/0.53    sP0(sK4,sK1) | ~v1_funct_2(sK4,sK1,sK2) | ~v1_funct_1(sK4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f76,f43])).
% 1.30/0.53  fof(f43,plain,(
% 1.30/0.53    k1_xboole_0 != sK2),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f76,plain,(
% 1.30/0.53    k1_xboole_0 = sK2 | sP0(sK4,sK1) | ~v1_funct_2(sK4,sK1,sK2) | ~v1_funct_1(sK4)),
% 1.30/0.53    inference(resolution,[],[f40,f64])).
% 1.30/0.53  fof(f64,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | sP0(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f25])).
% 1.30/0.53  fof(f25,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (sP0(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.30/0.53    inference(definition_folding,[],[f20,f24])).
% 1.30/0.53  fof(f24,plain,(
% 1.30/0.53    ! [X2,X0] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | ~sP0(X2,X0))),
% 1.30/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.53  fof(f20,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.30/0.53    inference(flattening,[],[f19])).
% 1.30/0.53  fof(f19,plain,(
% 1.30/0.53    ! [X0,X1,X2] : (((v2_funct_1(X2) <=> ! [X3,X4] : (X3 = X4 | (k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.30/0.53    inference(ennf_transformation,[],[f7])).
% 1.30/0.53  fof(f7,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v2_funct_1(X2) <=> ! [X3,X4] : ((k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0)) => X3 = X4))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_funct_2)).
% 1.30/0.53  fof(f40,plain,(
% 1.30/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f370,plain,(
% 1.30/0.53    ~sP0(sK4,sK1) | (~spl10_1 | ~spl10_3)),
% 1.30/0.53    inference(subsumption_resolution,[],[f368,f42])).
% 1.30/0.53  fof(f42,plain,(
% 1.30/0.53    r2_hidden(sK3,sK1)),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f368,plain,(
% 1.30/0.53    ~r2_hidden(sK3,sK1) | ~sP0(sK4,sK1) | (~spl10_1 | ~spl10_3)),
% 1.30/0.53    inference(resolution,[],[f366,f185])).
% 1.30/0.53  fof(f185,plain,(
% 1.30/0.53    r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),sK1) | (~spl10_1 | ~spl10_3)),
% 1.30/0.53    inference(backward_demodulation,[],[f108,f175])).
% 1.30/0.53  fof(f175,plain,(
% 1.30/0.53    k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = sK7(sK4,sK1,k1_funct_1(sK4,sK3)) | ~spl10_3),
% 1.30/0.53    inference(forward_demodulation,[],[f174,f95])).
% 1.30/0.53  fof(f95,plain,(
% 1.30/0.53    k1_funct_1(sK4,sK3) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3)))),
% 1.30/0.53    inference(resolution,[],[f94,f42])).
% 1.30/0.53  fof(f94,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0)))) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f93,f86])).
% 1.30/0.53  fof(f86,plain,(
% 1.30/0.53    v1_relat_1(sK4)),
% 1.30/0.53    inference(subsumption_resolution,[],[f79,f54])).
% 1.30/0.53  fof(f54,plain,(
% 1.30/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.30/0.53    inference(cnf_transformation,[],[f2])).
% 1.30/0.53  fof(f2,axiom,(
% 1.30/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.30/0.53  fof(f79,plain,(
% 1.30/0.53    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2))),
% 1.30/0.53    inference(resolution,[],[f40,f45])).
% 1.30/0.53  fof(f45,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f13])).
% 1.30/0.53  fof(f13,plain,(
% 1.30/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.30/0.53    inference(ennf_transformation,[],[f1])).
% 1.30/0.53  fof(f1,axiom,(
% 1.30/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.30/0.53  fof(f93,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0))) | ~v1_relat_1(sK4)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f92,f38])).
% 1.30/0.53  fof(f92,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | k1_funct_1(sK4,X0) = k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,X0))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.30/0.53    inference(resolution,[],[f91,f70])).
% 1.30/0.53  fof(f70,plain,(
% 1.30/0.53    ( ! [X6,X0,X1] : (~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(equality_resolution,[],[f48])).
% 1.30/0.53  fof(f48,plain,(
% 1.30/0.53    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f33])).
% 1.30/0.53  fof(f33,plain,(
% 1.30/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).
% 1.30/0.53  fof(f30,plain,(
% 1.30/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f31,plain,(
% 1.30/0.53    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f32,plain,(
% 1.30/0.53    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f29,plain,(
% 1.30/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.53    inference(rectify,[],[f28])).
% 1.30/0.53  fof(f28,plain,(
% 1.30/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.53    inference(nnf_transformation,[],[f15])).
% 1.30/0.53  fof(f15,plain,(
% 1.30/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.30/0.53    inference(flattening,[],[f14])).
% 1.30/0.53  fof(f14,plain,(
% 1.30/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.30/0.53    inference(ennf_transformation,[],[f3])).
% 1.30/0.53  fof(f3,axiom,(
% 1.30/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 1.30/0.53  fof(f91,plain,(
% 1.30/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,X0),k9_relat_1(sK4,sK1)) | ~r2_hidden(X0,sK1)) )),
% 1.30/0.53    inference(forward_demodulation,[],[f82,f90])).
% 1.30/0.53  fof(f90,plain,(
% 1.30/0.53    k2_relset_1(sK1,sK2,sK4) = k9_relat_1(sK4,sK1)),
% 1.30/0.53    inference(forward_demodulation,[],[f77,f75])).
% 1.30/0.53  fof(f75,plain,(
% 1.30/0.53    ( ! [X1] : (k7_relset_1(sK1,sK2,sK4,X1) = k9_relat_1(sK4,X1)) )),
% 1.30/0.53    inference(resolution,[],[f40,f66])).
% 1.30/0.53  fof(f66,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f21])).
% 1.30/0.53  fof(f21,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f5])).
% 1.30/0.53  % (16357)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.30/0.53  fof(f5,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.30/0.53  fof(f77,plain,(
% 1.30/0.53    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1)),
% 1.30/0.53    inference(resolution,[],[f40,f57])).
% 1.30/0.53  fof(f57,plain,(
% 1.30/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f18])).
% 1.30/0.53  fof(f18,plain,(
% 1.30/0.53    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.30/0.53    inference(ennf_transformation,[],[f6])).
% 1.30/0.53  fof(f6,axiom,(
% 1.30/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.30/0.53  fof(f82,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4))) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f81,f38])).
% 1.30/0.53  fof(f81,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) | ~v1_funct_1(sK4)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f80,f39])).
% 1.30/0.53  fof(f80,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) | ~v1_funct_2(sK4,sK1,sK2) | ~v1_funct_1(sK4)) )),
% 1.30/0.53    inference(subsumption_resolution,[],[f74,f43])).
% 1.30/0.53  fof(f74,plain,(
% 1.30/0.53    ( ! [X0] : (k1_xboole_0 = sK2 | ~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(sK1,sK2,sK4)) | ~v1_funct_2(sK4,sK1,sK2) | ~v1_funct_1(sK4)) )),
% 1.30/0.53    inference(resolution,[],[f40,f67])).
% 1.30/0.53  % (16354)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.30/0.53  fof(f67,plain,(
% 1.30/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f23])).
% 1.30/0.53  fof(f23,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.30/0.53    inference(flattening,[],[f22])).
% 1.30/0.53  fof(f22,plain,(
% 1.30/0.53    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.30/0.53    inference(ennf_transformation,[],[f8])).
% 1.30/0.53  fof(f8,axiom,(
% 1.30/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).
% 1.30/0.53  fof(f174,plain,(
% 1.30/0.53    sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3)))) | ~spl10_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f173,f86])).
% 1.30/0.53  fof(f173,plain,(
% 1.30/0.53    sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3)))) | ~v1_relat_1(sK4) | ~spl10_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f172,f38])).
% 1.30/0.53  fof(f172,plain,(
% 1.30/0.53    sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3)))) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl10_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f170,f41])).
% 1.30/0.53  fof(f41,plain,(
% 1.30/0.53    v2_funct_1(sK4)),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f170,plain,(
% 1.30/0.53    sK7(sK4,sK1,k1_funct_1(sK4,sK3)) = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK7(sK4,sK1,k1_funct_1(sK4,sK3)))) | ~v2_funct_1(sK4) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~spl10_3),
% 1.30/0.53    inference(resolution,[],[f121,f55])).
% 1.30/0.53  fof(f55,plain,(
% 1.30/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f17])).
% 1.30/0.53  fof(f17,plain,(
% 1.30/0.53    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.30/0.53    inference(flattening,[],[f16])).
% 1.30/0.53  fof(f16,plain,(
% 1.30/0.53    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.30/0.53    inference(ennf_transformation,[],[f4])).
% 1.30/0.53  fof(f4,axiom,(
% 1.30/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 1.30/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 1.30/0.53  fof(f121,plain,(
% 1.30/0.53    r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4)) | ~spl10_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f120])).
% 1.30/0.53  fof(f120,plain,(
% 1.30/0.53    spl10_3 <=> r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.30/0.53  fof(f108,plain,(
% 1.30/0.53    r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1) | ~spl10_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f107])).
% 1.30/0.53  fof(f107,plain,(
% 1.30/0.53    spl10_1 <=> r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1)),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.30/0.53  fof(f366,plain,(
% 1.30/0.53    ( ! [X0] : (~r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X0) | ~r2_hidden(sK3,X0) | ~sP0(sK4,X0)) ) | ~spl10_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f365,f44])).
% 1.30/0.53  fof(f44,plain,(
% 1.30/0.53    sK3 != k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))),
% 1.30/0.53    inference(cnf_transformation,[],[f27])).
% 1.30/0.53  fof(f365,plain,(
% 1.30/0.53    ( ! [X0] : (sK3 = k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) | ~r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X0) | ~r2_hidden(sK3,X0) | ~sP0(sK4,X0)) ) | ~spl10_3),
% 1.30/0.53    inference(equality_resolution,[],[f201])).
% 1.30/0.53  fof(f201,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_funct_1(sK4,sK3) != k1_funct_1(sK4,X0) | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = X0 | ~r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X1) | ~r2_hidden(X0,X1) | ~sP0(sK4,X1)) ) | ~spl10_3),
% 1.30/0.53    inference(subsumption_resolution,[],[f197,f41])).
% 1.30/0.53  fof(f197,plain,(
% 1.30/0.53    ( ! [X0,X1] : (k1_funct_1(sK4,sK3) != k1_funct_1(sK4,X0) | k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)) = X0 | ~r2_hidden(k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3)),X1) | ~r2_hidden(X0,X1) | ~v2_funct_1(sK4) | ~sP0(sK4,X1)) ) | ~spl10_3),
% 1.30/0.53    inference(superposition,[],[f59,f186])).
% 1.30/0.53  fof(f186,plain,(
% 1.30/0.53    k1_funct_1(sK4,sK3) = k1_funct_1(sK4,k1_funct_1(k2_funct_1(sK4),k1_funct_1(sK4,sK3))) | ~spl10_3),
% 1.30/0.53    inference(backward_demodulation,[],[f95,f175])).
% 1.30/0.53  fof(f59,plain,(
% 1.30/0.53    ( ! [X4,X0,X5,X1] : (k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | X4 = X5 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~v2_funct_1(X0) | ~sP0(X0,X1)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f37])).
% 1.30/0.53  fof(f37,plain,(
% 1.30/0.53    ! [X0,X1] : (((v2_funct_1(X0) | (sK8(X0,X1) != sK9(X0,X1) & k1_funct_1(X0,sK8(X0,X1)) = k1_funct_1(X0,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK8(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 1.30/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f35,f36])).
% 1.30/0.53  fof(f36,plain,(
% 1.30/0.53    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK8(X0,X1) != sK9(X0,X1) & k1_funct_1(X0,sK8(X0,X1)) = k1_funct_1(X0,sK9(X0,X1)) & r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK8(X0,X1),X1)))),
% 1.30/0.53    introduced(choice_axiom,[])).
% 1.30/0.53  fof(f35,plain,(
% 1.30/0.53    ! [X0,X1] : (((v2_funct_1(X0) | ? [X2,X3] : (X2 != X3 & k1_funct_1(X0,X2) = k1_funct_1(X0,X3) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X0,X4) != k1_funct_1(X0,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~v2_funct_1(X0))) | ~sP0(X0,X1))),
% 1.30/0.53    inference(rectify,[],[f34])).
% 1.30/0.53  fof(f34,plain,(
% 1.30/0.53    ! [X2,X0] : (((v2_funct_1(X2) | ? [X3,X4] : (X3 != X4 & k1_funct_1(X2,X3) = k1_funct_1(X2,X4) & r2_hidden(X4,X0) & r2_hidden(X3,X0))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X2,X3) != k1_funct_1(X2,X4) | ~r2_hidden(X4,X0) | ~r2_hidden(X3,X0)) | ~v2_funct_1(X2))) | ~sP0(X2,X0))),
% 1.30/0.53    inference(nnf_transformation,[],[f24])).
% 1.30/0.53  fof(f169,plain,(
% 1.30/0.53    ~spl10_2 | spl10_3),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f168])).
% 1.30/0.53  fof(f168,plain,(
% 1.30/0.53    $false | (~spl10_2 | spl10_3)),
% 1.30/0.53    inference(subsumption_resolution,[],[f167,f86])).
% 1.30/0.53  fof(f167,plain,(
% 1.30/0.53    ~v1_relat_1(sK4) | (~spl10_2 | spl10_3)),
% 1.30/0.53    inference(subsumption_resolution,[],[f166,f38])).
% 1.30/0.53  fof(f166,plain,(
% 1.30/0.53    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl10_2 | spl10_3)),
% 1.30/0.53    inference(subsumption_resolution,[],[f165,f113])).
% 1.30/0.53  fof(f113,plain,(
% 1.30/0.53    r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | ~spl10_2),
% 1.30/0.53    inference(avatar_component_clause,[],[f111])).
% 1.30/0.53  fof(f111,plain,(
% 1.30/0.53    spl10_2 <=> r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1))),
% 1.30/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.30/0.53  fof(f165,plain,(
% 1.30/0.53    ~r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl10_3),
% 1.30/0.53    inference(resolution,[],[f122,f72])).
% 1.30/0.53  fof(f72,plain,(
% 1.30/0.53    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(equality_resolution,[],[f46])).
% 1.30/0.53  fof(f46,plain,(
% 1.30/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f33])).
% 1.30/0.53  fof(f122,plain,(
% 1.30/0.53    ~r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),k1_relat_1(sK4)) | spl10_3),
% 1.30/0.53    inference(avatar_component_clause,[],[f120])).
% 1.30/0.53  fof(f149,plain,(
% 1.30/0.53    spl10_1),
% 1.30/0.53    inference(avatar_contradiction_clause,[],[f148])).
% 1.30/0.53  fof(f148,plain,(
% 1.30/0.53    $false | spl10_1),
% 1.30/0.53    inference(subsumption_resolution,[],[f146,f42])).
% 1.30/0.53  fof(f146,plain,(
% 1.30/0.53    ~r2_hidden(sK3,sK1) | spl10_1),
% 1.30/0.53    inference(resolution,[],[f145,f91])).
% 1.30/0.53  fof(f145,plain,(
% 1.30/0.53    ~r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | spl10_1),
% 1.30/0.53    inference(subsumption_resolution,[],[f144,f86])).
% 1.30/0.53  fof(f144,plain,(
% 1.30/0.53    ~r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | ~v1_relat_1(sK4) | spl10_1),
% 1.30/0.53    inference(subsumption_resolution,[],[f143,f38])).
% 1.30/0.53  fof(f143,plain,(
% 1.30/0.53    ~r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | spl10_1),
% 1.30/0.53    inference(resolution,[],[f109,f71])).
% 1.30/0.53  fof(f71,plain,(
% 1.30/0.53    ( ! [X6,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(equality_resolution,[],[f47])).
% 1.30/0.53  fof(f47,plain,(
% 1.30/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.30/0.53    inference(cnf_transformation,[],[f33])).
% 1.30/0.53  fof(f109,plain,(
% 1.30/0.53    ~r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1) | spl10_1),
% 1.30/0.53    inference(avatar_component_clause,[],[f107])).
% 1.30/0.53  fof(f114,plain,(
% 1.30/0.53    ~spl10_1 | spl10_2),
% 1.30/0.53    inference(avatar_split_clause,[],[f101,f111,f107])).
% 1.30/0.53  fof(f101,plain,(
% 1.30/0.53    r2_hidden(k1_funct_1(sK4,sK3),k9_relat_1(sK4,sK1)) | ~r2_hidden(sK7(sK4,sK1,k1_funct_1(sK4,sK3)),sK1)),
% 1.30/0.53    inference(superposition,[],[f91,f95])).
% 1.30/0.53  % SZS output end Proof for theBenchmark
% 1.30/0.53  % (16348)------------------------------
% 1.30/0.53  % (16348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (16348)Termination reason: Refutation
% 1.30/0.53  
% 1.30/0.53  % (16348)Memory used [KB]: 10874
% 1.30/0.53  % (16348)Time elapsed: 0.090 s
% 1.30/0.53  % (16348)------------------------------
% 1.30/0.53  % (16348)------------------------------
% 1.30/0.53  % (16351)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.30/0.53  % (16346)Success in time 0.169 s
%------------------------------------------------------------------------------
