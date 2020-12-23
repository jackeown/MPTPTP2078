%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t188_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:38 EDT 2019

% Result     : Theorem 210.52s
% Output     : Refutation 210.52s
% Verified   : 
% Statistics : Number of formulae       :  269 ( 939 expanded)
%              Number of leaves         :   40 ( 234 expanded)
%              Depth                    :   23
%              Number of atoms          :  861 (3353 expanded)
%              Number of equality atoms :  128 ( 578 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153473,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f140,f515,f3615,f3663,f3703,f3883,f3936,f6805,f6833,f15415,f15418,f15428,f16880,f153448])).

fof(f153448,plain,
    ( ~ spl13_6
    | spl13_245
    | ~ spl13_246
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(avatar_contradiction_clause,[],[f153447])).

fof(f153447,plain,
    ( $false
    | ~ spl13_6
    | ~ spl13_245
    | ~ spl13_246
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(subsumption_resolution,[],[f153430,f96262])).

fof(f96262,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2)),sK1)
    | ~ spl13_245
    | ~ spl13_246 ),
    inference(subsumption_resolution,[],[f96248,f3870])).

fof(f3870,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ spl13_245 ),
    inference(avatar_component_clause,[],[f3869])).

fof(f3869,plain,
    ( spl13_245
  <=> ~ v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_245])])).

fof(f96248,plain,
    ( m1_subset_1(sK9(k2_relat_1(sK2)),sK1)
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl13_246 ),
    inference(resolution,[],[f3882,f152])).

fof(f152,plain,(
    ! [X1] :
      ( m1_subset_1(sK9(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f91,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK9(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',d1_xboole_0)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t1_subset)).

fof(f3882,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k2_relat_1(sK2))
        | m1_subset_1(X0,sK1) )
    | ~ spl13_246 ),
    inference(avatar_component_clause,[],[f3881])).

fof(f3881,plain,
    ( spl13_246
  <=> ! [X0] :
        ( m1_subset_1(X0,sK1)
        | ~ m1_subset_1(X0,k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_246])])).

fof(f153430,plain,
    ( ~ m1_subset_1(sK9(k2_relat_1(sK2)),sK1)
    | ~ spl13_6
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(trivial_inequality_removal,[],[f153387])).

fof(f153387,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ m1_subset_1(sK9(k2_relat_1(sK2)),sK1)
    | ~ spl13_6
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(superposition,[],[f3769,f153332])).

fof(f153332,plain,
    ( k1_tarski(sK9(k2_relat_1(sK2))) = k2_relat_1(sK2)
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(resolution,[],[f153329,f116])).

fof(f116,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',d1_tarski)).

fof(f153329,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK9(k2_relat_1(sK2)),k1_tarski(X7))
        | k1_tarski(X7) = k2_relat_1(sK2) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(subsumption_resolution,[],[f153328,f6804])).

fof(f6804,plain,
    ( ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),X0) )
    | ~ spl13_448 ),
    inference(avatar_component_clause,[],[f6803])).

fof(f6803,plain,
    ( spl13_448
  <=> ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | k2_relat_1(sK2) = X0
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_448])])).

fof(f153328,plain,
    ( ! [X7] :
        ( k1_tarski(X7) = k2_relat_1(sK2)
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),k1_tarski(X7))
        | sK6(sK2,k1_tarski(X7)) = sK9(k2_relat_1(sK2)) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(subsumption_resolution,[],[f153253,f114])).

fof(f114,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f153253,plain,
    ( ! [X7] :
        ( sK9(k2_relat_1(sK2)) != X7
        | k1_tarski(X7) = k2_relat_1(sK2)
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),k1_tarski(X7))
        | sK6(sK2,k1_tarski(X7)) = sK9(k2_relat_1(sK2)) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(duplicate_literal_removal,[],[f153177])).

fof(f153177,plain,
    ( ! [X7] :
        ( sK9(k2_relat_1(sK2)) != X7
        | k1_tarski(X7) = k2_relat_1(sK2)
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),k1_tarski(X7))
        | sK6(sK2,k1_tarski(X7)) = sK9(k2_relat_1(sK2))
        | k1_tarski(X7) = k2_relat_1(sK2) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_448
    | ~ spl13_1152 ),
    inference(superposition,[],[f6804,f152858])).

fof(f152858,plain,
    ( ! [X1] :
        ( sK6(sK2,k1_tarski(X1)) = sK9(k2_relat_1(sK2))
        | sK6(sK2,k1_tarski(X1)) = X1
        | k1_tarski(X1) = k2_relat_1(sK2) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_1152 ),
    inference(duplicate_literal_removal,[],[f152785])).

fof(f152785,plain,
    ( ! [X1] :
        ( sK6(sK2,k1_tarski(X1)) = sK9(k2_relat_1(sK2))
        | k1_tarski(X1) = k2_relat_1(sK2)
        | sK6(sK2,k1_tarski(X1)) = X1
        | sK6(sK2,k1_tarski(X1)) = X1
        | k1_tarski(X1) = k2_relat_1(sK2) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_1152 ),
    inference(superposition,[],[f27450,f28629])).

fof(f28629,plain,
    ( ! [X14] :
        ( k1_funct_1(sK2,sK8(sK2,k1_tarski(X14))) = sK9(k2_relat_1(sK2))
        | sK6(sK2,k1_tarski(X14)) = X14
        | k1_tarski(X14) = k2_relat_1(sK2) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_1152 ),
    inference(resolution,[],[f7404,f18665])).

fof(f18665,plain,
    ( ! [X9] :
        ( ~ r2_hidden(X9,k1_relat_1(sK2))
        | k1_funct_1(sK2,X9) = sK9(k2_relat_1(sK2)) )
    | ~ spl13_245
    | ~ spl13_446
    | ~ spl13_1152 ),
    inference(forward_demodulation,[],[f18656,f6767])).

fof(f6767,plain,
    ( k1_funct_1(sK2,sK7(sK2,sK9(k2_relat_1(sK2)))) = sK9(k2_relat_1(sK2))
    | ~ spl13_245 ),
    inference(subsumption_resolution,[],[f6762,f3870])).

fof(f6762,plain,
    ( k1_funct_1(sK2,sK7(sK2,sK9(k2_relat_1(sK2)))) = sK9(k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f3779,f87])).

fof(f3779,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK2))
      | k1_funct_1(sK2,sK7(sK2,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f3775,f69])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t188_funct_2)).

fof(f3775,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | k1_funct_1(sK2,sK7(sK2,X1)) = X1
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f162,f112])).

fof(f112,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK7(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',d5_funct_1)).

fof(f162,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f100,f71])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',cc1_relset_1)).

fof(f18656,plain,
    ( ! [X9] :
        ( k1_funct_1(sK2,X9) = k1_funct_1(sK2,sK7(sK2,sK9(k2_relat_1(sK2))))
        | ~ r2_hidden(X9,k1_relat_1(sK2)) )
    | ~ spl13_446
    | ~ spl13_1152 ),
    inference(resolution,[],[f15427,f6798])).

fof(f6798,plain,
    ( r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_446 ),
    inference(avatar_component_clause,[],[f6797])).

fof(f6797,plain,
    ( spl13_446
  <=> r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_446])])).

fof(f15427,plain,
    ( ! [X37,X36] :
        ( ~ r2_hidden(X37,k1_relat_1(sK2))
        | k1_funct_1(sK2,X36) = k1_funct_1(sK2,X37)
        | ~ r2_hidden(X36,k1_relat_1(sK2)) )
    | ~ spl13_1152 ),
    inference(avatar_component_clause,[],[f15426])).

fof(f15426,plain,
    ( spl13_1152
  <=> ! [X36,X37] :
        ( ~ r2_hidden(X36,k1_relat_1(sK2))
        | k1_funct_1(sK2,X36) = k1_funct_1(sK2,X37)
        | ~ r2_hidden(X37,k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1152])])).

fof(f7404,plain,(
    ! [X3] :
      ( r2_hidden(sK8(sK2,k1_tarski(X3)),k1_relat_1(sK2))
      | k1_tarski(X3) = k2_relat_1(sK2)
      | sK6(sK2,k1_tarski(X3)) = X3 ) ),
    inference(resolution,[],[f3778,f114])).

fof(f3778,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK6(sK2,X0),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(subsumption_resolution,[],[f3774,f69])).

fof(f3774,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | r2_hidden(sK8(sK2,X0),k1_relat_1(sK2))
      | r2_hidden(sK6(sK2,X0),X0)
      | k2_relat_1(sK2) = X0 ) ),
    inference(resolution,[],[f162,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK8(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f27450,plain,(
    ! [X7] :
      ( k1_funct_1(sK2,sK8(sK2,k1_tarski(X7))) = sK6(sK2,k1_tarski(X7))
      | k1_tarski(X7) = k2_relat_1(sK2)
      | sK6(sK2,k1_tarski(X7)) = X7 ) ),
    inference(resolution,[],[f5446,f114])).

fof(f5446,plain,(
    ! [X29] :
      ( r2_hidden(sK6(sK2,X29),X29)
      | k1_funct_1(sK2,sK8(sK2,X29)) = sK6(sK2,X29)
      | k2_relat_1(sK2) = X29 ) ),
    inference(subsumption_resolution,[],[f5441,f69])).

fof(f5441,plain,(
    ! [X29] :
      ( ~ v1_funct_1(sK2)
      | k1_funct_1(sK2,sK8(sK2,X29)) = sK6(sK2,X29)
      | r2_hidden(sK6(sK2,X29),X29)
      | k2_relat_1(sK2) = X29 ) ),
    inference(resolution,[],[f83,f162])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK8(X0,X1)) = sK6(X0,X1)
      | r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3769,plain,
    ( ! [X3] :
        ( k1_tarski(X3) != k2_relat_1(sK2)
        | ~ m1_subset_1(X3,sK1) )
    | ~ spl13_6 ),
    inference(backward_demodulation,[],[f430,f139])).

fof(f139,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k1_tarski(X3) )
    | ~ spl13_6 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl13_6
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,sK1)
        | k2_relset_1(sK0,sK1,sK2) != k1_tarski(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_6])])).

fof(f430,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f71,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',redefinition_k2_relset_1)).

fof(f16880,plain,
    ( spl13_1
    | ~ spl13_2
    | spl13_245
    | ~ spl13_1132
    | ~ spl13_1134 ),
    inference(avatar_contradiction_clause,[],[f16879])).

fof(f16879,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132
    | ~ spl13_1134 ),
    inference(subsumption_resolution,[],[f16878,f119])).

fof(f119,plain,
    ( ~ v3_funct_1(sK2)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl13_1
  <=> ~ v3_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f16878,plain,
    ( v3_funct_1(sK2)
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132
    | ~ spl13_1134 ),
    inference(subsumption_resolution,[],[f16877,f162])).

fof(f16877,plain,
    ( ~ v1_relat_1(sK2)
    | v3_funct_1(sK2)
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132
    | ~ spl13_1134 ),
    inference(subsumption_resolution,[],[f16876,f69])).

fof(f16876,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2)
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132
    | ~ spl13_1134 ),
    inference(subsumption_resolution,[],[f16869,f16796])).

fof(f16796,plain,
    ( k1_funct_1(sK2,sK4(sK2)) = sK3
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1134 ),
    inference(subsumption_resolution,[],[f16793,f15449])).

fof(f15449,plain,
    ( ~ v1_xboole_0(k1_tarski(sK3))
    | ~ spl13_2
    | ~ spl13_245 ),
    inference(backward_demodulation,[],[f435,f3870])).

fof(f435,plain,
    ( k1_tarski(sK3) = k2_relat_1(sK2)
    | ~ spl13_2 ),
    inference(forward_demodulation,[],[f430,f128])).

fof(f128,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
    | ~ spl13_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl13_2
  <=> k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_2])])).

fof(f16793,plain,
    ( v1_xboole_0(k1_tarski(sK3))
    | k1_funct_1(sK2,sK4(sK2)) = sK3
    | ~ spl13_2
    | ~ spl13_1134 ),
    inference(resolution,[],[f16519,f158])).

fof(f158,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_tarski(X4))
      | v1_xboole_0(k1_tarski(X4))
      | X4 = X5 ) ),
    inference(resolution,[],[f92,f114])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t2_subset)).

fof(f16519,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k1_tarski(sK3))
    | ~ spl13_2
    | ~ spl13_1134 ),
    inference(forward_demodulation,[],[f15285,f435])).

fof(f15285,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k2_relat_1(sK2))
    | ~ spl13_1134 ),
    inference(avatar_component_clause,[],[f15284])).

fof(f15284,plain,
    ( spl13_1134
  <=> m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1134])])).

fof(f16869,plain,
    ( k1_funct_1(sK2,sK4(sK2)) != sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2)
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132 ),
    inference(superposition,[],[f80,f16843])).

fof(f16843,plain,
    ( k1_funct_1(sK2,sK5(sK2)) = sK3
    | ~ spl13_2
    | ~ spl13_245
    | ~ spl13_1132 ),
    inference(subsumption_resolution,[],[f16840,f15449])).

fof(f16840,plain,
    ( v1_xboole_0(k1_tarski(sK3))
    | k1_funct_1(sK2,sK5(sK2)) = sK3
    | ~ spl13_2
    | ~ spl13_1132 ),
    inference(resolution,[],[f16520,f158])).

fof(f16520,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k1_tarski(sK3))
    | ~ spl13_2
    | ~ spl13_1132 ),
    inference(forward_demodulation,[],[f15276,f435])).

fof(f15276,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2))
    | ~ spl13_1132 ),
    inference(avatar_component_clause,[],[f15275])).

fof(f15275,plain,
    ( spl13_1132
  <=> m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1132])])).

fof(f80,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(X0)) != k1_funct_1(X0,sK5(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v3_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v3_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => k1_funct_1(X0,X1) = k1_funct_1(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',d16_funct_1)).

fof(f15428,plain,
    ( ~ spl13_1
    | spl13_1152 ),
    inference(avatar_split_clause,[],[f4878,f15426,f118])).

fof(f4878,plain,(
    ! [X37,X36] :
      ( ~ r2_hidden(X36,k1_relat_1(sK2))
      | ~ r2_hidden(X37,k1_relat_1(sK2))
      | k1_funct_1(sK2,X36) = k1_funct_1(sK2,X37)
      | ~ v3_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f4873,f69])).

fof(f4873,plain,(
    ! [X37,X36] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X36,k1_relat_1(sK2))
      | ~ r2_hidden(X37,k1_relat_1(sK2))
      | k1_funct_1(sK2,X36) = k1_funct_1(sK2,X37)
      | ~ v3_funct_1(sK2) ) ),
    inference(resolution,[],[f77,f162])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
      | ~ v3_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15418,plain,
    ( spl13_0
    | spl13_1134 ),
    inference(avatar_split_clause,[],[f15417,f15284,f121])).

fof(f121,plain,
    ( spl13_0
  <=> v3_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f15417,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k2_relat_1(sK2))
    | v3_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f15416,f162])).

fof(f15416,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f6724,f69])).

fof(f6724,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK4(sK2)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2) ),
    inference(resolution,[],[f3781,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v3_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3781,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | m1_subset_1(k1_funct_1(sK2,X3),k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f3777,f69])).

fof(f3777,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ v1_funct_1(sK2)
      | m1_subset_1(k1_funct_1(sK2,X3),k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f162,f2464])).

fof(f2464,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | m1_subset_1(k1_funct_1(X2,X3),k2_relat_1(X2)) ) ),
    inference(resolution,[],[f111,f91])).

fof(f111,plain,(
    ! [X0,X3] :
      ( r2_hidden(k1_funct_1(X0,X3),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X3),X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | k1_funct_1(X0,X3) != X2
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15415,plain,
    ( spl13_0
    | spl13_1132 ),
    inference(avatar_split_clause,[],[f15414,f15275,f121])).

fof(f15414,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2))
    | v3_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f15413,f162])).

fof(f15413,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f6725,f69])).

fof(f6725,plain,
    ( m1_subset_1(k1_funct_1(sK2,sK5(sK2)),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v3_funct_1(sK2) ),
    inference(resolution,[],[f3781,f79])).

fof(f79,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v3_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6833,plain,
    ( spl13_49
    | spl13_245
    | spl13_447 ),
    inference(avatar_contradiction_clause,[],[f6832])).

fof(f6832,plain,
    ( $false
    | ~ spl13_49
    | ~ spl13_245
    | ~ spl13_447 ),
    inference(subsumption_resolution,[],[f6831,f6712])).

fof(f6712,plain,
    ( m1_subset_1(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_245 ),
    inference(subsumption_resolution,[],[f6707,f3870])).

fof(f6707,plain,
    ( m1_subset_1(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f3780,f87])).

fof(f3780,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK2))
      | m1_subset_1(sK7(sK2,X2),k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f3776,f69])).

fof(f3776,plain,(
    ! [X2] :
      ( ~ v1_funct_1(sK2)
      | ~ r2_hidden(X2,k2_relat_1(sK2))
      | m1_subset_1(sK7(sK2,X2),k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f162,f2475])).

fof(f2475,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | m1_subset_1(sK7(X2,X3),k1_relat_1(X2)) ) ),
    inference(resolution,[],[f113,f91])).

fof(f113,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK7(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f6831,plain,
    ( ~ m1_subset_1(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_49
    | ~ spl13_447 ),
    inference(subsumption_resolution,[],[f6828,f482])).

fof(f482,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_49 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl13_49
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_49])])).

fof(f6828,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ m1_subset_1(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_447 ),
    inference(resolution,[],[f6801,f92])).

fof(f6801,plain,
    ( ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
    | ~ spl13_447 ),
    inference(avatar_component_clause,[],[f6800])).

fof(f6800,plain,
    ( spl13_447
  <=> ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_447])])).

fof(f6805,plain,
    ( ~ spl13_447
    | spl13_448
    | spl13_245 ),
    inference(avatar_split_clause,[],[f6795,f3869,f6803,f6800])).

fof(f6795,plain,
    ( ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
        | ~ r2_hidden(sK9(k2_relat_1(sK2)),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl13_245 ),
    inference(inner_rewriting,[],[f6794])).

fof(f6794,plain,
    ( ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
        | ~ r2_hidden(sK6(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl13_245 ),
    inference(subsumption_resolution,[],[f6793,f162])).

fof(f6793,plain,
    ( ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK6(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl13_245 ),
    inference(subsumption_resolution,[],[f6789,f69])).

fof(f6789,plain,
    ( ! [X0] :
        ( sK6(sK2,X0) != sK9(k2_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(sK7(sK2,sK9(k2_relat_1(sK2))),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK6(sK2,X0),X0)
        | k2_relat_1(sK2) = X0 )
    | ~ spl13_245 ),
    inference(superposition,[],[f81,f6767])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(X0,X3) != sK6(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3936,plain,
    ( spl13_49
    | ~ spl13_244 ),
    inference(avatar_contradiction_clause,[],[f3935])).

fof(f3935,plain,
    ( $false
    | ~ spl13_49
    | ~ spl13_244 ),
    inference(subsumption_resolution,[],[f3929,f482])).

fof(f3929,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_244 ),
    inference(resolution,[],[f3923,f87])).

fof(f3923,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(sK2))
    | ~ spl13_244 ),
    inference(subsumption_resolution,[],[f3922,f162])).

fof(f3922,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl13_244 ),
    inference(subsumption_resolution,[],[f3921,f69])).

fof(f3921,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl13_244 ),
    inference(subsumption_resolution,[],[f3918,f146])).

fof(f146,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(resolution,[],[f88,f74])).

fof(f74,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',dt_o_0_0_xboole_0)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3918,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(sK2,X1),o_0_0_xboole_0)
        | ~ v1_funct_1(sK2)
        | ~ r2_hidden(X1,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl13_244 ),
    inference(superposition,[],[f111,f3895])).

fof(f3895,plain,
    ( k2_relat_1(sK2) = o_0_0_xboole_0
    | ~ spl13_244 ),
    inference(resolution,[],[f3873,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f142,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t6_boole)).

fof(f142,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f75,f74])).

fof(f3873,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl13_244 ),
    inference(avatar_component_clause,[],[f3872])).

fof(f3872,plain,
    ( spl13_244
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_244])])).

fof(f3883,plain,
    ( spl13_244
    | spl13_246 ),
    inference(avatar_split_clause,[],[f3876,f3881,f3872])).

fof(f3876,plain,(
    ! [X0] :
      ( m1_subset_1(X0,sK1)
      | v1_xboole_0(k2_relat_1(sK2))
      | ~ m1_subset_1(X0,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f3849,f92])).

fof(f3849,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | m1_subset_1(X0,sK1) ) ),
    inference(forward_demodulation,[],[f3842,f430])).

fof(f3842,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f71,f1092])).

fof(f1092,plain,(
    ! [X14,X12,X15,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X13,X14)))
      | ~ r2_hidden(X15,k2_relset_1(X13,X14,X12))
      | m1_subset_1(X15,X14) ) ),
    inference(resolution,[],[f104,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t4_subset)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',dt_k2_relset_1)).

fof(f3703,plain,
    ( ~ spl13_16
    | ~ spl13_48
    | spl13_169 ),
    inference(avatar_contradiction_clause,[],[f3702])).

fof(f3702,plain,
    ( $false
    | ~ spl13_16
    | ~ spl13_48
    | ~ spl13_169 ),
    inference(subsumption_resolution,[],[f3701,f74])).

fof(f3701,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl13_16
    | ~ spl13_48
    | ~ spl13_169 ),
    inference(forward_demodulation,[],[f3684,f898])).

fof(f898,plain,(
    o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0)) ),
    inference(resolution,[],[f885,f145])).

fof(f885,plain,(
    v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f174,f87])).

fof(f174,plain,(
    ! [X1] : ~ r2_hidden(X1,sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f171,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',existence_m1_subset_1)).

fof(f171,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f106,f74])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',t5_subset)).

fof(f3684,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl13_16
    | ~ spl13_48
    | ~ spl13_169 ),
    inference(backward_demodulation,[],[f3672,f2118])).

fof(f2118,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0))))
    | ~ spl13_169 ),
    inference(avatar_component_clause,[],[f2117])).

fof(f2117,plain,
    ( spl13_169
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_169])])).

fof(f3672,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(resolution,[],[f3656,f145])).

fof(f3656,plain,
    ( v1_xboole_0(k2_relat_1(o_0_0_xboole_0))
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(resolution,[],[f2480,f87])).

fof(f2480,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(o_0_0_xboole_0))
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f2479,f274])).

fof(f274,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl13_16 ),
    inference(backward_demodulation,[],[f267,f162])).

fof(f267,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl13_16 ),
    inference(resolution,[],[f253,f145])).

fof(f253,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl13_16
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_16])])).

fof(f2479,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(o_0_0_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(o_0_0_xboole_0)) )
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f2478,f269])).

fof(f269,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl13_16 ),
    inference(backward_demodulation,[],[f267,f69])).

fof(f2478,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(o_0_0_xboole_0)
        | ~ v1_relat_1(o_0_0_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(o_0_0_xboole_0)) )
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f2477,f146])).

fof(f2477,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(o_0_0_xboole_0,X0),o_0_0_xboole_0)
        | ~ v1_funct_1(o_0_0_xboole_0)
        | ~ v1_relat_1(o_0_0_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(o_0_0_xboole_0)) )
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(superposition,[],[f113,f1766])).

fof(f1766,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(resolution,[],[f1755,f145])).

fof(f1755,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ spl13_16
    | ~ spl13_48 ),
    inference(forward_demodulation,[],[f485,f661])).

fof(f661,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl13_16 ),
    inference(resolution,[],[f253,f145])).

fof(f485,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl13_48 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl13_48
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_48])])).

fof(f3663,plain,
    ( ~ spl13_16
    | ~ spl13_48
    | spl13_159 ),
    inference(avatar_contradiction_clause,[],[f3662])).

fof(f3662,plain,
    ( $false
    | ~ spl13_16
    | ~ spl13_48
    | ~ spl13_159 ),
    inference(subsumption_resolution,[],[f3656,f2078])).

fof(f2078,plain,
    ( ~ v1_xboole_0(k2_relat_1(o_0_0_xboole_0))
    | ~ spl13_159 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f2077,plain,
    ( spl13_159
  <=> ~ v1_xboole_0(k2_relat_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_159])])).

fof(f3615,plain,
    ( ~ spl13_16
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(avatar_contradiction_clause,[],[f3614])).

fof(f3614,plain,
    ( $false
    | ~ spl13_16
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(subsumption_resolution,[],[f3613,f72])).

fof(f72,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f3613,plain,
    ( v1_xboole_0(sK1)
    | ~ spl13_16
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(subsumption_resolution,[],[f3612,f73])).

fof(f73,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f3612,plain,
    ( v1_xboole_0(sK0)
    | v1_xboole_0(sK1)
    | ~ spl13_16
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(resolution,[],[f3559,f664])).

fof(f664,plain,
    ( v1_funct_2(o_0_0_xboole_0,sK0,sK1)
    | ~ spl13_16 ),
    inference(backward_demodulation,[],[f661,f70])).

fof(f70,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f3559,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(o_0_0_xboole_0,X1,X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X0) )
    | ~ spl13_16
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(subsumption_resolution,[],[f3192,f3558])).

fof(f3558,plain,
    ( ! [X6] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X6))
    | ~ spl13_158
    | ~ spl13_168 ),
    inference(forward_demodulation,[],[f3541,f3204])).

fof(f3204,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl13_158 ),
    inference(resolution,[],[f2081,f145])).

fof(f2081,plain,
    ( v1_xboole_0(k2_relat_1(o_0_0_xboole_0))
    | ~ spl13_158 ),
    inference(avatar_component_clause,[],[f2080])).

fof(f2080,plain,
    ( spl13_158
  <=> v1_xboole_0(k2_relat_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_158])])).

fof(f3541,plain,
    ( ! [X6] : m1_subset_1(k2_relat_1(o_0_0_xboole_0),k1_zfmisc_1(X6))
    | ~ spl13_168 ),
    inference(superposition,[],[f2676,f3524])).

fof(f3524,plain,
    ( ! [X5] : o_0_0_xboole_0 = sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X5)))
    | ~ spl13_168 ),
    inference(resolution,[],[f3512,f145])).

fof(f3512,plain,
    ( ! [X0] : v1_xboole_0(sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0))))
    | ~ spl13_168 ),
    inference(subsumption_resolution,[],[f3507,f164])).

fof(f164,plain,(
    ! [X2,X3] : v1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) ),
    inference(resolution,[],[f100,f89])).

fof(f3507,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0))))
        | v1_xboole_0(sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X0)))) )
    | ~ spl13_168 ),
    inference(resolution,[],[f3503,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',fc8_relat_1)).

fof(f3503,plain,
    ( ! [X6] : v1_xboole_0(k1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X6)))))
    | ~ spl13_168 ),
    inference(resolution,[],[f3373,f87])).

fof(f3373,plain,
    ( ! [X4,X3] : ~ r2_hidden(X3,k1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X4)))))
    | ~ spl13_168 ),
    inference(resolution,[],[f2156,f2539])).

fof(f2539,plain,(
    ! [X0,X1] : m1_subset_1(k1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f2536,f89])).

fof(f2536,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f103,f372])).

fof(f372,plain,(
    ! [X4,X5] : k1_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k1_relset_1(X4,X5,sK10(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ),
    inference(resolution,[],[f101,f89])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',redefinition_k1_relset_1)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',dt_k1_relset_1)).

fof(f2156,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl13_168 ),
    inference(backward_demodulation,[],[f2153,f2151])).

fof(f2151,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0)))))
        | ~ r2_hidden(X1,X0) )
    | ~ spl13_168 ),
    inference(resolution,[],[f2121,f106])).

fof(f2121,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0))))
    | ~ spl13_168 ),
    inference(avatar_component_clause,[],[f2120])).

fof(f2120,plain,
    ( spl13_168
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_168])])).

fof(f2153,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(k2_relat_1(o_0_0_xboole_0)))
    | ~ spl13_168 ),
    inference(resolution,[],[f2121,f145])).

fof(f2676,plain,(
    ! [X0,X1] : m1_subset_1(k2_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1)) ),
    inference(subsumption_resolution,[],[f2672,f89])).

fof(f2672,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1)))),k1_zfmisc_1(X1))
      | ~ m1_subset_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X0,X1))),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f104,f377])).

fof(f377,plain,(
    ! [X4,X5] : k2_relset_1(X4,X5,sK10(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k2_relat_1(sK10(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ),
    inference(resolution,[],[f102,f89])).

fof(f3192,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(o_0_0_xboole_0,X1,X0) )
    | ~ spl13_16 ),
    inference(subsumption_resolution,[],[f3154,f74])).

fof(f3154,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(X0)
        | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(o_0_0_xboole_0,X1,X0)
        | ~ v1_xboole_0(o_0_0_xboole_0) )
    | ~ spl13_16 ),
    inference(resolution,[],[f93,f269])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t188_funct_2.p',cc6_funct_2)).

fof(f515,plain,
    ( spl13_17
    | ~ spl13_48 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl13_17
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f513,f250])).

fof(f250,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl13_17 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl13_17
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_17])])).

fof(f513,plain,
    ( v1_xboole_0(sK2)
    | ~ spl13_48 ),
    inference(subsumption_resolution,[],[f508,f162])).

fof(f508,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl13_48 ),
    inference(resolution,[],[f485,f76])).

fof(f140,plain,
    ( ~ spl13_1
    | spl13_6 ),
    inference(avatar_split_clause,[],[f66,f138,f118])).

fof(f66,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | k2_relset_1(sK0,sK1,sK2) != k1_tarski(X3)
      | ~ v3_funct_1(sK2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f129,plain,
    ( spl13_0
    | spl13_2 ),
    inference(avatar_split_clause,[],[f68,f127,f121])).

fof(f68,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k1_tarski(sK3)
    | v3_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
