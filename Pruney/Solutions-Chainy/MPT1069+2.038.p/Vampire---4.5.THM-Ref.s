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
% DateTime   : Thu Dec  3 13:07:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 360 expanded)
%              Number of leaves         :   48 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  671 (1835 expanded)
%              Number of equality atoms :  144 ( 403 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f611,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f168,f181,f216,f219,f284,f369,f392,f415,f416,f419,f428,f483,f502,f522,f559,f583,f593,f610])).

fof(f610,plain,
    ( ~ spl10_9
    | ~ spl10_12
    | ~ spl10_25
    | ~ spl10_40
    | spl10_48 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_25
    | ~ spl10_40
    | spl10_48 ),
    inference(subsumption_resolution,[],[f608,f174])).

fof(f174,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl10_12
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f608,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl10_9
    | ~ spl10_25
    | ~ spl10_40
    | spl10_48 ),
    inference(forward_demodulation,[],[f607,f501])).

fof(f501,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl10_40
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f607,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl10_9
    | ~ spl10_25
    | spl10_48 ),
    inference(subsumption_resolution,[],[f606,f282])).

fof(f282,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl10_25
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f606,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_9
    | spl10_48 ),
    inference(subsumption_resolution,[],[f597,f136])).

fof(f136,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl10_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f597,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_48 ),
    inference(resolution,[],[f591,f85])).

fof(f85,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK6(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK6(X0,X1),X1) )
              & ( ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
                  & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK6(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK8(X0,X5)) = X5
                    & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f40,f43,f42,f41])).

fof(f41,plain,(
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
              ( k1_funct_1(X0,X3) != sK6(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK6(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK6(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK6(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK6(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f591,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))
    | spl10_48 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl10_48
  <=> r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f593,plain,
    ( ~ spl10_48
    | ~ spl10_41
    | spl10_47 ),
    inference(avatar_split_clause,[],[f584,f580,f519,f589])).

fof(f519,plain,
    ( spl10_41
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f580,plain,
    ( spl10_47
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f584,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))
    | ~ spl10_41
    | spl10_47 ),
    inference(unit_resulting_resolution,[],[f582,f528])).

fof(f528,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,k1_relat_1(sK4)) )
    | ~ spl10_41 ),
    inference(resolution,[],[f521,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f521,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f519])).

fof(f582,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl10_47 ),
    inference(avatar_component_clause,[],[f580])).

fof(f583,plain,
    ( ~ spl10_47
    | ~ spl10_6
    | ~ spl10_13
    | ~ spl10_16
    | spl10_42 ),
    inference(avatar_split_clause,[],[f577,f556,f212,f197,f119,f580])).

fof(f119,plain,
    ( spl10_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f197,plain,
    ( spl10_13
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f212,plain,
    ( spl10_16
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f556,plain,
    ( spl10_42
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f577,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl10_6
    | ~ spl10_13
    | ~ spl10_16
    | spl10_42 ),
    inference(unit_resulting_resolution,[],[f214,f121,f199,f558,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f558,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_42 ),
    inference(avatar_component_clause,[],[f556])).

fof(f199,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f197])).

fof(f121,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f214,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f212])).

fof(f559,plain,
    ( ~ spl10_42
    | spl10_1
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f553,f314,f94,f556])).

fof(f94,plain,
    ( spl10_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f314,plain,
    ( spl10_30
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f553,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_1
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f96,f316])).

fof(f316,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f314])).

fof(f96,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f522,plain,
    ( spl10_41
    | ~ spl10_24
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f516,f480,f275,f519])).

fof(f275,plain,
    ( spl10_24
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f480,plain,
    ( spl10_38
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f516,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_24
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f482,f277])).

fof(f277,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f275])).

fof(f482,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f480])).

fof(f502,plain,
    ( spl10_40
    | ~ spl10_23
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f497,f294,f270,f499])).

fof(f270,plain,
    ( spl10_23
  <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f294,plain,
    ( spl10_27
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f497,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_23
    | ~ spl10_27 ),
    inference(forward_demodulation,[],[f272,f296])).

fof(f296,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f294])).

fof(f272,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f483,plain,
    ( spl10_38
    | ~ spl10_3
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f473,f202,f104,f480])).

fof(f104,plain,
    ( spl10_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f202,plain,
    ( spl10_14
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f473,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl10_3
    | ~ spl10_14 ),
    inference(backward_demodulation,[],[f106,f204])).

fof(f204,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f202])).

fof(f106,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f428,plain,
    ( spl10_30
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10 ),
    inference(avatar_split_clause,[],[f422,f139,f134,f129,f124,f119,f114,f109,f104,f99,f314])).

fof(f99,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f109,plain,
    ( spl10_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f114,plain,
    ( spl10_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f124,plain,
    ( spl10_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f129,plain,
    ( spl10_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f139,plain,
    ( spl10_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f422,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | ~ spl10_7
    | ~ spl10_8
    | ~ spl10_9
    | spl10_10 ),
    inference(unit_resulting_resolution,[],[f141,f136,f121,f111,f101,f131,f126,f116,f106,f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f116,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f114])).

fof(f126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f131,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f111,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f141,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f139])).

fof(f419,plain,
    ( spl10_27
    | ~ spl10_7
    | ~ spl10_8
    | spl10_26 ),
    inference(avatar_split_clause,[],[f418,f290,f129,f124,f294])).

fof(f290,plain,
    ( spl10_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f418,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_7
    | ~ spl10_8
    | spl10_26 ),
    inference(subsumption_resolution,[],[f417,f291])).

fof(f291,plain,
    ( k1_xboole_0 != sK2
    | spl10_26 ),
    inference(avatar_component_clause,[],[f290])).

fof(f417,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f408,f131])).

fof(f408,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl10_7 ),
    inference(resolution,[],[f126,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
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
    inference(nnf_transformation,[],[f33])).

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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f416,plain,
    ( spl10_23
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f406,f124,f270])).

fof(f406,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f126,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f415,plain,
    ( spl10_24
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f405,f124,f275])).

fof(f405,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f126,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f392,plain,
    ( spl10_14
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f383,f114,f202])).

fof(f383,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_5 ),
    inference(resolution,[],[f116,f76])).

fof(f369,plain,
    ( spl10_10
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl10_10
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f341,f60])).

fof(f60,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f341,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_10
    | ~ spl10_26 ),
    inference(backward_demodulation,[],[f141,f292])).

fof(f292,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f290])).

fof(f284,plain,
    ( spl10_25
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f256,f124,f280])).

fof(f256,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f126,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f219,plain,
    ( spl10_13
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f191,f114,f197])).

fof(f191,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_5 ),
    inference(resolution,[],[f116,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f216,plain,
    ( spl10_16
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f188,f114,f212])).

fof(f188,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_5 ),
    inference(resolution,[],[f116,f74])).

fof(f181,plain,
    ( spl10_12
    | ~ spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f178,f165,f109,f172])).

fof(f165,plain,
    ( spl10_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f178,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_4
    | spl10_11 ),
    inference(unit_resulting_resolution,[],[f111,f167,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f167,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f168,plain,
    ( ~ spl10_11
    | spl10_2 ),
    inference(avatar_split_clause,[],[f163,f99,f165])).

fof(f163,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f101,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f142,plain,(
    ~ spl10_10 ),
    inference(avatar_split_clause,[],[f50,f139])).

fof(f50,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f137,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f51,f134])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f52,f129])).

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f54,f119])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f112,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f56,f109])).

fof(f56,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f57,f104])).

fof(f57,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f58,f99])).

fof(f58,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f59,f94])).

fof(f59,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (2422)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (2447)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (2447)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (2435)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (2433)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (2449)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f611,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f168,f181,f216,f219,f284,f369,f392,f415,f416,f419,f428,f483,f502,f522,f559,f583,f593,f610])).
% 0.20/0.52  fof(f610,plain,(
% 0.20/0.52    ~spl10_9 | ~spl10_12 | ~spl10_25 | ~spl10_40 | spl10_48),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f609])).
% 0.20/0.52  fof(f609,plain,(
% 0.20/0.52    $false | (~spl10_9 | ~spl10_12 | ~spl10_25 | ~spl10_40 | spl10_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f608,f174])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    r2_hidden(sK5,sK1) | ~spl10_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f172])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    spl10_12 <=> r2_hidden(sK5,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.52  fof(f608,plain,(
% 0.20/0.52    ~r2_hidden(sK5,sK1) | (~spl10_9 | ~spl10_25 | ~spl10_40 | spl10_48)),
% 0.20/0.52    inference(forward_demodulation,[],[f607,f501])).
% 0.20/0.52  fof(f501,plain,(
% 0.20/0.52    sK1 = k1_relat_1(sK3) | ~spl10_40),
% 0.20/0.52    inference(avatar_component_clause,[],[f499])).
% 0.20/0.52  fof(f499,plain,(
% 0.20/0.52    spl10_40 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.20/0.52  fof(f607,plain,(
% 0.20/0.52    ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl10_9 | ~spl10_25 | spl10_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f606,f282])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    v1_relat_1(sK3) | ~spl10_25),
% 0.20/0.52    inference(avatar_component_clause,[],[f280])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    spl10_25 <=> v1_relat_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.20/0.52  fof(f606,plain,(
% 0.20/0.52    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl10_9 | spl10_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f597,f136])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    v1_funct_1(sK3) | ~spl10_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f134])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    spl10_9 <=> v1_funct_1(sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.52  fof(f597,plain,(
% 0.20/0.52    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl10_48),
% 0.20/0.52    inference(resolution,[],[f591,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f40,f43,f42,f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(rectify,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.52  fof(f591,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) | spl10_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f589])).
% 0.20/0.52  fof(f589,plain,(
% 0.20/0.52    spl10_48 <=> r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.20/0.52  fof(f593,plain,(
% 0.20/0.52    ~spl10_48 | ~spl10_41 | spl10_47),
% 0.20/0.52    inference(avatar_split_clause,[],[f584,f580,f519,f589])).
% 0.20/0.52  fof(f519,plain,(
% 0.20/0.52    spl10_41 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.20/0.52  fof(f580,plain,(
% 0.20/0.52    spl10_47 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.20/0.52  fof(f584,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) | (~spl10_41 | spl10_47)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f582,f528])).
% 0.20/0.52  fof(f528,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,k1_relat_1(sK4))) ) | ~spl10_41),
% 0.20/0.52    inference(resolution,[],[f521,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f521,plain,(
% 0.20/0.52    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~spl10_41),
% 0.20/0.52    inference(avatar_component_clause,[],[f519])).
% 0.20/0.52  fof(f582,plain,(
% 0.20/0.52    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl10_47),
% 0.20/0.52    inference(avatar_component_clause,[],[f580])).
% 0.20/0.52  fof(f583,plain,(
% 0.20/0.52    ~spl10_47 | ~spl10_6 | ~spl10_13 | ~spl10_16 | spl10_42),
% 0.20/0.52    inference(avatar_split_clause,[],[f577,f556,f212,f197,f119,f580])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl10_6 <=> v1_funct_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    spl10_13 <=> v5_relat_1(sK4,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    spl10_16 <=> v1_relat_1(sK4)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.20/0.52  fof(f556,plain,(
% 0.20/0.52    spl10_42 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.20/0.53  fof(f577,plain,(
% 0.20/0.53    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl10_6 | ~spl10_13 | ~spl10_16 | spl10_42)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f214,f121,f199,f558,f69])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,axiom,(
% 0.20/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.53  fof(f558,plain,(
% 0.20/0.53    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl10_42),
% 0.20/0.53    inference(avatar_component_clause,[],[f556])).
% 0.20/0.53  fof(f199,plain,(
% 0.20/0.53    v5_relat_1(sK4,sK0) | ~spl10_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f197])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    v1_funct_1(sK4) | ~spl10_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f119])).
% 0.20/0.53  fof(f214,plain,(
% 0.20/0.53    v1_relat_1(sK4) | ~spl10_16),
% 0.20/0.53    inference(avatar_component_clause,[],[f212])).
% 0.20/0.53  fof(f559,plain,(
% 0.20/0.53    ~spl10_42 | spl10_1 | ~spl10_30),
% 0.20/0.53    inference(avatar_split_clause,[],[f553,f314,f94,f556])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl10_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.53  fof(f314,plain,(
% 0.20/0.53    spl10_30 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.20/0.53  fof(f553,plain,(
% 0.20/0.53    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl10_1 | ~spl10_30)),
% 0.20/0.53    inference(backward_demodulation,[],[f96,f316])).
% 0.20/0.53  fof(f316,plain,(
% 0.20/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl10_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f314])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl10_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f94])).
% 0.20/0.53  fof(f522,plain,(
% 0.20/0.53    spl10_41 | ~spl10_24 | ~spl10_38),
% 0.20/0.53    inference(avatar_split_clause,[],[f516,f480,f275,f519])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    spl10_24 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.20/0.53  fof(f480,plain,(
% 0.20/0.53    spl10_38 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.20/0.53  fof(f516,plain,(
% 0.20/0.53    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl10_24 | ~spl10_38)),
% 0.20/0.53    inference(backward_demodulation,[],[f482,f277])).
% 0.20/0.53  fof(f277,plain,(
% 0.20/0.53    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl10_24),
% 0.20/0.53    inference(avatar_component_clause,[],[f275])).
% 0.20/0.53  fof(f482,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl10_38),
% 0.20/0.53    inference(avatar_component_clause,[],[f480])).
% 0.20/0.53  fof(f502,plain,(
% 0.20/0.53    spl10_40 | ~spl10_23 | ~spl10_27),
% 0.20/0.53    inference(avatar_split_clause,[],[f497,f294,f270,f499])).
% 0.20/0.53  fof(f270,plain,(
% 0.20/0.53    spl10_23 <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    spl10_27 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.20/0.53  fof(f497,plain,(
% 0.20/0.53    sK1 = k1_relat_1(sK3) | (~spl10_23 | ~spl10_27)),
% 0.20/0.53    inference(forward_demodulation,[],[f272,f296])).
% 0.20/0.53  fof(f296,plain,(
% 0.20/0.53    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl10_27),
% 0.20/0.53    inference(avatar_component_clause,[],[f294])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl10_23),
% 0.20/0.53    inference(avatar_component_clause,[],[f270])).
% 0.20/0.53  fof(f483,plain,(
% 0.20/0.53    spl10_38 | ~spl10_3 | ~spl10_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f473,f202,f104,f480])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl10_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.53  fof(f202,plain,(
% 0.20/0.53    spl10_14 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.53  fof(f473,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl10_3 | ~spl10_14)),
% 0.20/0.53    inference(backward_demodulation,[],[f106,f204])).
% 0.20/0.53  fof(f204,plain,(
% 0.20/0.53    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f202])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl10_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f428,plain,(
% 0.20/0.53    spl10_30 | spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f422,f139,f134,f129,f124,f119,f114,f109,f104,f99,f314])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl10_2 <=> k1_xboole_0 = sK1),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl10_4 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.53  fof(f114,plain,(
% 0.20/0.53    spl10_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    spl10_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl10_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.53  fof(f139,plain,(
% 0.20/0.53    spl10_10 <=> v1_xboole_0(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.53  fof(f422,plain,(
% 0.20/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f141,f136,f121,f111,f101,f131,f126,f116,f106,f73])).
% 0.20/0.53  fof(f73,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f27])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.20/0.53    inference(flattening,[],[f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f114])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f124])).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK1,sK2) | ~spl10_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f129])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    k1_xboole_0 != sK1 | spl10_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    m1_subset_1(sK5,sK1) | ~spl10_4),
% 0.20/0.53    inference(avatar_component_clause,[],[f109])).
% 0.20/0.53  fof(f141,plain,(
% 0.20/0.53    ~v1_xboole_0(sK2) | spl10_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f139])).
% 0.20/0.53  fof(f419,plain,(
% 0.20/0.53    spl10_27 | ~spl10_7 | ~spl10_8 | spl10_26),
% 0.20/0.53    inference(avatar_split_clause,[],[f418,f290,f129,f124,f294])).
% 0.20/0.53  fof(f290,plain,(
% 0.20/0.53    spl10_26 <=> k1_xboole_0 = sK2),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.53  fof(f418,plain,(
% 0.20/0.53    sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl10_7 | ~spl10_8 | spl10_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f417,f291])).
% 0.20/0.53  fof(f291,plain,(
% 0.20/0.53    k1_xboole_0 != sK2 | spl10_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f290])).
% 0.20/0.53  fof(f417,plain,(
% 0.20/0.53    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | (~spl10_7 | ~spl10_8)),
% 0.20/0.53    inference(subsumption_resolution,[],[f408,f131])).
% 0.20/0.53  fof(f408,plain,(
% 0.20/0.53    sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | ~spl10_7),
% 0.20/0.53    inference(resolution,[],[f126,f78])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f49])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(nnf_transformation,[],[f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(flattening,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.53  fof(f416,plain,(
% 0.20/0.53    spl10_23 | ~spl10_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f406,f124,f270])).
% 0.20/0.53  fof(f406,plain,(
% 0.20/0.53    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl10_7),
% 0.20/0.53    inference(resolution,[],[f126,f76])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f30])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.53  fof(f415,plain,(
% 0.20/0.53    spl10_24 | ~spl10_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f405,f124,f275])).
% 0.20/0.53  fof(f405,plain,(
% 0.20/0.53    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl10_7),
% 0.20/0.53    inference(resolution,[],[f126,f75])).
% 0.20/0.53  fof(f75,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f29])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.53  fof(f392,plain,(
% 0.20/0.53    spl10_14 | ~spl10_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f383,f114,f202])).
% 0.20/0.53  fof(f383,plain,(
% 0.20/0.53    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_5),
% 0.20/0.53    inference(resolution,[],[f116,f76])).
% 0.20/0.53  fof(f369,plain,(
% 0.20/0.53    spl10_10 | ~spl10_26),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f368])).
% 0.20/0.53  fof(f368,plain,(
% 0.20/0.53    $false | (spl10_10 | ~spl10_26)),
% 0.20/0.53    inference(subsumption_resolution,[],[f341,f60])).
% 0.20/0.53  fof(f60,plain,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    v1_xboole_0(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.53  fof(f341,plain,(
% 0.20/0.53    ~v1_xboole_0(k1_xboole_0) | (spl10_10 | ~spl10_26)),
% 0.20/0.53    inference(backward_demodulation,[],[f141,f292])).
% 0.20/0.53  fof(f292,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | ~spl10_26),
% 0.20/0.53    inference(avatar_component_clause,[],[f290])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    spl10_25 | ~spl10_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f256,f124,f280])).
% 0.20/0.53  fof(f256,plain,(
% 0.20/0.53    v1_relat_1(sK3) | ~spl10_7),
% 0.20/0.53    inference(resolution,[],[f126,f74])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.53  fof(f219,plain,(
% 0.20/0.53    spl10_13 | ~spl10_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f191,f114,f197])).
% 0.20/0.53  fof(f191,plain,(
% 0.20/0.53    v5_relat_1(sK4,sK0) | ~spl10_5),
% 0.20/0.53    inference(resolution,[],[f116,f77])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.53    inference(ennf_transformation,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.53    inference(pure_predicate_removal,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.53  fof(f216,plain,(
% 0.20/0.53    spl10_16 | ~spl10_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f188,f114,f212])).
% 0.20/0.53  fof(f188,plain,(
% 0.20/0.53    v1_relat_1(sK4) | ~spl10_5),
% 0.20/0.53    inference(resolution,[],[f116,f74])).
% 0.20/0.53  fof(f181,plain,(
% 0.20/0.53    spl10_12 | ~spl10_4 | spl10_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f178,f165,f109,f172])).
% 0.20/0.53  fof(f165,plain,(
% 0.20/0.53    spl10_11 <=> v1_xboole_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.53  fof(f178,plain,(
% 0.20/0.53    r2_hidden(sK5,sK1) | (~spl10_4 | spl10_11)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f167,f68])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f22])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(flattening,[],[f21])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.53  fof(f167,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1) | spl10_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f165])).
% 0.20/0.53  fof(f168,plain,(
% 0.20/0.53    ~spl10_11 | spl10_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f163,f99,f165])).
% 0.20/0.53  fof(f163,plain,(
% 0.20/0.53    ~v1_xboole_0(sK1) | spl10_2),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f101,f61])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ~spl10_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f50,f139])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    ~v1_xboole_0(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f37,f36,f35,f34])).
% 0.20/0.53  fof(f34,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.53    inference(flattening,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.53    inference(ennf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f13])).
% 0.20/0.53  fof(f13,conjecture,(
% 0.20/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    spl10_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f51,f134])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    v1_funct_1(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    spl10_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f52,f129])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl10_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f53,f124])).
% 0.20/0.53  fof(f53,plain,(
% 0.20/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl10_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f54,f119])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    v1_funct_1(sK4)),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    spl10_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f55,f114])).
% 0.20/0.53  fof(f55,plain,(
% 0.20/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    spl10_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f56,f109])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    m1_subset_1(sK5,sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl10_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f57,f104])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    ~spl10_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f58,f99])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    k1_xboole_0 != sK1),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ~spl10_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f59,f94])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.53    inference(cnf_transformation,[],[f38])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (2447)------------------------------
% 0.20/0.53  % (2447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2447)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (2447)Memory used [KB]: 6652
% 0.20/0.53  % (2447)Time elapsed: 0.096 s
% 0.20/0.53  % (2447)------------------------------
% 0.20/0.53  % (2447)------------------------------
% 0.20/0.53  % (2421)Success in time 0.171 s
%------------------------------------------------------------------------------
