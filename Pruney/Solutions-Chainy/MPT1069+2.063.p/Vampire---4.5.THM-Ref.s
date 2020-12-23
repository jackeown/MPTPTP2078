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
% DateTime   : Thu Dec  3 13:07:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 366 expanded)
%              Number of leaves         :   49 ( 173 expanded)
%              Depth                    :   15
%              Number of atoms          :  682 (1851 expanded)
%              Number of equality atoms :  144 ( 403 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f617,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f170,f183,f220,f236,f302,f375,f398,f421,f422,f425,f434,f489,f508,f528,f565,f589,f599,f616])).

fof(f616,plain,
    ( ~ spl10_9
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_40
    | spl10_48 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl10_9
    | ~ spl10_12
    | ~ spl10_22
    | ~ spl10_40
    | spl10_48 ),
    inference(subsumption_resolution,[],[f614,f176])).

fof(f176,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_12
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f614,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl10_9
    | ~ spl10_22
    | ~ spl10_40
    | spl10_48 ),
    inference(forward_demodulation,[],[f613,f507])).

fof(f507,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f505])).

fof(f505,plain,
    ( spl10_40
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f613,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl10_9
    | ~ spl10_22
    | spl10_48 ),
    inference(subsumption_resolution,[],[f612,f271])).

fof(f271,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl10_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f612,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl10_9
    | spl10_48 ),
    inference(subsumption_resolution,[],[f603,f138])).

fof(f138,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl10_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f603,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl10_48 ),
    inference(resolution,[],[f597,f87])).

fof(f87,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f41,f44,f43,f42])).

fof(f42,plain,(
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

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK6(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK8(X0,X5)) = X5
        & r2_hidden(sK8(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f597,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))
    | spl10_48 ),
    inference(avatar_component_clause,[],[f595])).

fof(f595,plain,
    ( spl10_48
  <=> r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f599,plain,
    ( ~ spl10_48
    | ~ spl10_41
    | spl10_47 ),
    inference(avatar_split_clause,[],[f590,f586,f525,f595])).

fof(f525,plain,
    ( spl10_41
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f586,plain,
    ( spl10_47
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).

fof(f590,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))
    | ~ spl10_41
    | spl10_47 ),
    inference(unit_resulting_resolution,[],[f588,f534])).

fof(f534,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | r2_hidden(X0,k1_relat_1(sK4)) )
    | ~ spl10_41 ),
    inference(resolution,[],[f527,f73])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f527,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f525])).

fof(f588,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl10_47 ),
    inference(avatar_component_clause,[],[f586])).

fof(f589,plain,
    ( ~ spl10_47
    | ~ spl10_6
    | ~ spl10_13
    | ~ spl10_14
    | spl10_42 ),
    inference(avatar_split_clause,[],[f583,f562,f204,f199,f121,f586])).

fof(f121,plain,
    ( spl10_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f199,plain,
    ( spl10_13
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f204,plain,
    ( spl10_14
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f562,plain,
    ( spl10_42
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f583,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl10_6
    | ~ spl10_13
    | ~ spl10_14
    | spl10_42 ),
    inference(unit_resulting_resolution,[],[f201,f123,f206,f564,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f564,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_42 ),
    inference(avatar_component_clause,[],[f562])).

fof(f206,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f204])).

fof(f123,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f201,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f565,plain,
    ( ~ spl10_42
    | spl10_1
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f559,f319,f96,f562])).

fof(f96,plain,
    ( spl10_1
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f319,plain,
    ( spl10_30
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f559,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl10_1
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f98,f321])).

fof(f321,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f98,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f528,plain,
    ( spl10_41
    | ~ spl10_25
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f522,f486,f284,f525])).

fof(f284,plain,
    ( spl10_25
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).

fof(f486,plain,
    ( spl10_38
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f522,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl10_25
    | ~ spl10_38 ),
    inference(backward_demodulation,[],[f488,f286])).

fof(f286,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_25 ),
    inference(avatar_component_clause,[],[f284])).

fof(f488,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f486])).

fof(f508,plain,
    ( spl10_40
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(avatar_split_clause,[],[f503,f297,f279,f505])).

fof(f279,plain,
    ( spl10_24
  <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f297,plain,
    ( spl10_27
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f503,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl10_24
    | ~ spl10_27 ),
    inference(forward_demodulation,[],[f281,f299])).

fof(f299,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f281,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f279])).

fof(f489,plain,
    ( spl10_38
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(avatar_split_clause,[],[f479,f209,f106,f486])).

fof(f106,plain,
    ( spl10_3
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f209,plain,
    ( spl10_15
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f479,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl10_3
    | ~ spl10_15 ),
    inference(backward_demodulation,[],[f108,f211])).

fof(f211,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f209])).

fof(f108,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f434,plain,
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
    inference(avatar_split_clause,[],[f428,f141,f136,f131,f126,f121,f116,f111,f106,f101,f319])).

fof(f101,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f111,plain,
    ( spl10_4
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f116,plain,
    ( spl10_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f126,plain,
    ( spl10_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f131,plain,
    ( spl10_8
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f141,plain,
    ( spl10_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f428,plain,
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
    inference(unit_resulting_resolution,[],[f143,f138,f123,f113,f103,f133,f128,f118,f108,f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f118,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f113,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f143,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f425,plain,
    ( spl10_27
    | ~ spl10_7
    | ~ spl10_8
    | spl10_26 ),
    inference(avatar_split_clause,[],[f424,f293,f131,f126,f297])).

fof(f293,plain,
    ( spl10_26
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f424,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_7
    | ~ spl10_8
    | spl10_26 ),
    inference(subsumption_resolution,[],[f423,f294])).

fof(f294,plain,
    ( k1_xboole_0 != sK2
    | spl10_26 ),
    inference(avatar_component_clause,[],[f293])).

fof(f423,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f413,f133])).

fof(f413,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | ~ spl10_7 ),
    inference(resolution,[],[f128,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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

fof(f422,plain,
    ( spl10_24
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f411,f126,f279])).

fof(f411,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f128,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f421,plain,
    ( spl10_25
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f410,f126,f284])).

fof(f410,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl10_7 ),
    inference(resolution,[],[f128,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f398,plain,
    ( spl10_15
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f388,f116,f209])).

fof(f388,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl10_5 ),
    inference(resolution,[],[f118,f78])).

fof(f375,plain,
    ( spl10_10
    | ~ spl10_26 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl10_10
    | ~ spl10_26 ),
    inference(subsumption_resolution,[],[f347,f61])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f347,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_10
    | ~ spl10_26 ),
    inference(backward_demodulation,[],[f143,f295])).

fof(f295,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f293])).

fof(f302,plain,
    ( spl10_22
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f301,f126,f269])).

fof(f301,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f265,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f265,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | ~ spl10_7 ),
    inference(resolution,[],[f128,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f236,plain,
    ( spl10_13
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f235,f116,f199])).

fof(f235,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f195,f70])).

fof(f195,plain,
    ( v1_relat_1(sK4)
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | ~ spl10_5 ),
    inference(resolution,[],[f118,f62])).

fof(f220,plain,
    ( spl10_14
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f192,f116,f204])).

fof(f192,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl10_5 ),
    inference(resolution,[],[f118,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f183,plain,
    ( spl10_12
    | ~ spl10_4
    | spl10_11 ),
    inference(avatar_split_clause,[],[f180,f167,f111,f174])).

fof(f167,plain,
    ( spl10_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f180,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_4
    | spl10_11 ),
    inference(unit_resulting_resolution,[],[f113,f169,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f169,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f167])).

fof(f170,plain,
    ( ~ spl10_11
    | spl10_2 ),
    inference(avatar_split_clause,[],[f165,f101,f167])).

fof(f165,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f103,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f144,plain,(
    ~ spl10_10 ),
    inference(avatar_split_clause,[],[f51,f141])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f38,f37,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f37,plain,
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

fof(f38,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f139,plain,(
    spl10_9 ),
    inference(avatar_split_clause,[],[f52,f136])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f134,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f53,f131])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f129,plain,(
    spl10_7 ),
    inference(avatar_split_clause,[],[f54,f126])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f57,f111])).

fof(f57,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f58,f106])).

fof(f58,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f104,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f59,f101])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f60,f96])).

fof(f60,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:16:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (19549)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.48  % (19541)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.48  % (19541)Refutation not found, incomplete strategy% (19541)------------------------------
% 0.20/0.48  % (19541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19549)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % (19541)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (19541)Memory used [KB]: 10746
% 0.20/0.49  % (19541)Time elapsed: 0.076 s
% 0.20/0.49  % (19541)------------------------------
% 0.20/0.49  % (19541)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f617,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f170,f183,f220,f236,f302,f375,f398,f421,f422,f425,f434,f489,f508,f528,f565,f589,f599,f616])).
% 0.20/0.49  fof(f616,plain,(
% 0.20/0.49    ~spl10_9 | ~spl10_12 | ~spl10_22 | ~spl10_40 | spl10_48),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f615])).
% 0.20/0.49  fof(f615,plain,(
% 0.20/0.49    $false | (~spl10_9 | ~spl10_12 | ~spl10_22 | ~spl10_40 | spl10_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f614,f176])).
% 0.20/0.49  fof(f176,plain,(
% 0.20/0.49    r2_hidden(sK5,sK1) | ~spl10_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    spl10_12 <=> r2_hidden(sK5,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 0.20/0.49  fof(f614,plain,(
% 0.20/0.49    ~r2_hidden(sK5,sK1) | (~spl10_9 | ~spl10_22 | ~spl10_40 | spl10_48)),
% 0.20/0.49    inference(forward_demodulation,[],[f613,f507])).
% 0.20/0.49  fof(f507,plain,(
% 0.20/0.49    sK1 = k1_relat_1(sK3) | ~spl10_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f505])).
% 0.20/0.49  fof(f505,plain,(
% 0.20/0.49    spl10_40 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.20/0.49  fof(f613,plain,(
% 0.20/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl10_9 | ~spl10_22 | spl10_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f612,f271])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~spl10_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f269])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    spl10_22 <=> v1_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.20/0.49  fof(f612,plain,(
% 0.20/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl10_9 | spl10_48)),
% 0.20/0.49    inference(subsumption_resolution,[],[f603,f138])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    v1_funct_1(sK3) | ~spl10_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    spl10_9 <=> v1_funct_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.20/0.49  fof(f603,plain,(
% 0.20/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl10_48),
% 0.20/0.49    inference(resolution,[],[f597,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & ((sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f41,f44,f43,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK6(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK6(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK6(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK6(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK6(X0,X1) = k1_funct_1(X0,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK8(X0,X5)) = X5 & r2_hidden(sK8(X0,X5),k1_relat_1(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(rectify,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.49    inference(flattening,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.49  fof(f597,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) | spl10_48),
% 0.20/0.49    inference(avatar_component_clause,[],[f595])).
% 0.20/0.49  fof(f595,plain,(
% 0.20/0.49    spl10_48 <=> r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.20/0.49  fof(f599,plain,(
% 0.20/0.49    ~spl10_48 | ~spl10_41 | spl10_47),
% 0.20/0.49    inference(avatar_split_clause,[],[f590,f586,f525,f595])).
% 0.20/0.49  fof(f525,plain,(
% 0.20/0.49    spl10_41 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.20/0.49  fof(f586,plain,(
% 0.20/0.49    spl10_47 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_47])])).
% 0.20/0.49  fof(f590,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k2_relat_1(sK3)) | (~spl10_41 | spl10_47)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f588,f534])).
% 0.20/0.49  fof(f534,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | r2_hidden(X0,k1_relat_1(sK4))) ) | ~spl10_41),
% 0.20/0.49    inference(resolution,[],[f527,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f47,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(rectify,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.49  fof(f527,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~spl10_41),
% 0.20/0.49    inference(avatar_component_clause,[],[f525])).
% 0.20/0.49  fof(f588,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl10_47),
% 0.20/0.49    inference(avatar_component_clause,[],[f586])).
% 0.20/0.49  fof(f589,plain,(
% 0.20/0.49    ~spl10_47 | ~spl10_6 | ~spl10_13 | ~spl10_14 | spl10_42),
% 0.20/0.49    inference(avatar_split_clause,[],[f583,f562,f204,f199,f121,f586])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl10_6 <=> v1_funct_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl10_13 <=> v1_relat_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    spl10_14 <=> v5_relat_1(sK4,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.20/0.49  fof(f562,plain,(
% 0.20/0.49    spl10_42 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).
% 0.20/0.49  fof(f583,plain,(
% 0.20/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl10_6 | ~spl10_13 | ~spl10_14 | spl10_42)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f201,f123,f206,f564,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.49  fof(f564,plain,(
% 0.20/0.49    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl10_42),
% 0.20/0.49    inference(avatar_component_clause,[],[f562])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    v5_relat_1(sK4,sK0) | ~spl10_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f204])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    v1_funct_1(sK4) | ~spl10_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    v1_relat_1(sK4) | ~spl10_13),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f565,plain,(
% 0.20/0.49    ~spl10_42 | spl10_1 | ~spl10_30),
% 0.20/0.49    inference(avatar_split_clause,[],[f559,f319,f96,f562])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl10_1 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.49  fof(f319,plain,(
% 0.20/0.49    spl10_30 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).
% 0.20/0.49  fof(f559,plain,(
% 0.20/0.49    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl10_1 | ~spl10_30)),
% 0.20/0.49    inference(backward_demodulation,[],[f98,f321])).
% 0.20/0.49  fof(f321,plain,(
% 0.20/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | ~spl10_30),
% 0.20/0.49    inference(avatar_component_clause,[],[f319])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl10_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f528,plain,(
% 0.20/0.49    spl10_41 | ~spl10_25 | ~spl10_38),
% 0.20/0.49    inference(avatar_split_clause,[],[f522,f486,f284,f525])).
% 0.20/0.49  fof(f284,plain,(
% 0.20/0.49    spl10_25 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_25])])).
% 0.20/0.49  fof(f486,plain,(
% 0.20/0.49    spl10_38 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.20/0.49  fof(f522,plain,(
% 0.20/0.49    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl10_25 | ~spl10_38)),
% 0.20/0.49    inference(backward_demodulation,[],[f488,f286])).
% 0.20/0.49  fof(f286,plain,(
% 0.20/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl10_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f284])).
% 0.20/0.49  fof(f488,plain,(
% 0.20/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl10_38),
% 0.20/0.49    inference(avatar_component_clause,[],[f486])).
% 0.20/0.49  fof(f508,plain,(
% 0.20/0.49    spl10_40 | ~spl10_24 | ~spl10_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f503,f297,f279,f505])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    spl10_24 <=> k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    spl10_27 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.20/0.49  fof(f503,plain,(
% 0.20/0.49    sK1 = k1_relat_1(sK3) | (~spl10_24 | ~spl10_27)),
% 0.20/0.49    inference(forward_demodulation,[],[f281,f299])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl10_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f297])).
% 0.20/0.49  fof(f281,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl10_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f279])).
% 0.20/0.49  fof(f489,plain,(
% 0.20/0.49    spl10_38 | ~spl10_3 | ~spl10_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f479,f209,f106,f486])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl10_3 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    spl10_15 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.20/0.49  fof(f479,plain,(
% 0.20/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl10_3 | ~spl10_15)),
% 0.20/0.49    inference(backward_demodulation,[],[f108,f211])).
% 0.20/0.49  fof(f211,plain,(
% 0.20/0.49    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f209])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl10_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f434,plain,(
% 0.20/0.49    spl10_30 | spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f428,f141,f136,f131,f126,f121,f116,f111,f106,f101,f319])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl10_2 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl10_4 <=> m1_subset_1(sK5,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    spl10_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    spl10_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    spl10_8 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    spl10_10 <=> v1_xboole_0(sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.20/0.49  fof(f428,plain,(
% 0.20/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5 | ~spl10_6 | ~spl10_7 | ~spl10_8 | ~spl10_9 | spl10_10)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f143,f138,f123,f113,f103,f133,f128,f118,f108,f76])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.20/0.49    inference(flattening,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl10_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f116])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl10_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f126])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    v1_funct_2(sK3,sK1,sK2) | ~spl10_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f131])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | spl10_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    m1_subset_1(sK5,sK1) | ~spl10_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ~v1_xboole_0(sK2) | spl10_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f141])).
% 0.20/0.49  fof(f425,plain,(
% 0.20/0.49    spl10_27 | ~spl10_7 | ~spl10_8 | spl10_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f424,f293,f131,f126,f297])).
% 0.20/0.49  fof(f293,plain,(
% 0.20/0.49    spl10_26 <=> k1_xboole_0 = sK2),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 0.20/0.49  fof(f424,plain,(
% 0.20/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl10_7 | ~spl10_8 | spl10_26)),
% 0.20/0.49    inference(subsumption_resolution,[],[f423,f294])).
% 0.20/0.49  fof(f294,plain,(
% 0.20/0.49    k1_xboole_0 != sK2 | spl10_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f293])).
% 0.20/0.49  fof(f423,plain,(
% 0.20/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | (~spl10_7 | ~spl10_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f413,f133])).
% 0.20/0.49  fof(f413,plain,(
% 0.20/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | ~spl10_7),
% 0.20/0.49    inference(resolution,[],[f128,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.49  fof(f422,plain,(
% 0.20/0.49    spl10_24 | ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f411,f126,f279])).
% 0.20/0.49  fof(f411,plain,(
% 0.20/0.49    k1_relat_1(sK3) = k1_relset_1(sK1,sK2,sK3) | ~spl10_7),
% 0.20/0.49    inference(resolution,[],[f128,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.49  fof(f421,plain,(
% 0.20/0.49    spl10_25 | ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f410,f126,f284])).
% 0.20/0.49  fof(f410,plain,(
% 0.20/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl10_7),
% 0.20/0.49    inference(resolution,[],[f128,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.49  fof(f398,plain,(
% 0.20/0.49    spl10_15 | ~spl10_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f388,f116,f209])).
% 0.20/0.49  fof(f388,plain,(
% 0.20/0.49    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl10_5),
% 0.20/0.49    inference(resolution,[],[f118,f78])).
% 0.20/0.49  fof(f375,plain,(
% 0.20/0.49    spl10_10 | ~spl10_26),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f374])).
% 0.20/0.49  fof(f374,plain,(
% 0.20/0.49    $false | (spl10_10 | ~spl10_26)),
% 0.20/0.49    inference(subsumption_resolution,[],[f347,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f347,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | (spl10_10 | ~spl10_26)),
% 0.20/0.49    inference(backward_demodulation,[],[f143,f295])).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    k1_xboole_0 = sK2 | ~spl10_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f293])).
% 0.20/0.49  fof(f302,plain,(
% 0.20/0.49    spl10_22 | ~spl10_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f301,f126,f269])).
% 0.20/0.49  fof(f301,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~spl10_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f265,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK2)) | ~spl10_7),
% 0.20/0.49    inference(resolution,[],[f128,f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl10_13 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f235,f116,f199])).
% 0.20/0.50  fof(f235,plain,(
% 0.20/0.50    v1_relat_1(sK4) | ~spl10_5),
% 0.20/0.50    inference(subsumption_resolution,[],[f195,f70])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    v1_relat_1(sK4) | ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f118,f62])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl10_14 | ~spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f192,f116,f204])).
% 0.20/0.50  fof(f192,plain,(
% 0.20/0.50    v5_relat_1(sK4,sK0) | ~spl10_5),
% 0.20/0.50    inference(resolution,[],[f118,f79])).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f183,plain,(
% 0.20/0.50    spl10_12 | ~spl10_4 | spl10_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f180,f167,f111,f174])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    spl10_11 <=> v1_xboole_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    r2_hidden(sK5,sK1) | (~spl10_4 | spl10_11)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f113,f169,f71])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(flattening,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | spl10_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f167])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ~spl10_11 | spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f165,f101,f167])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ~v1_xboole_0(sK1) | spl10_2),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f103,f63])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ~spl10_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f51,f141])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ~v1_xboole_0(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f38,f37,f36,f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,negated_conjecture,(
% 0.20/0.50    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.50    inference(negated_conjecture,[],[f14])).
% 0.20/0.50  fof(f14,conjecture,(
% 0.20/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl10_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f52,f136])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    v1_funct_1(sK3)),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f134,plain,(
% 0.20/0.50    spl10_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f53,f131])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    spl10_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f54,f126])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl10_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f55,f121])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    v1_funct_1(sK4)),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl10_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f56,f116])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl10_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f111])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    m1_subset_1(sK5,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    spl10_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f58,f106])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    ~spl10_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f101])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    k1_xboole_0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  fof(f99,plain,(
% 0.20/0.50    ~spl10_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f60,f96])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.20/0.50    inference(cnf_transformation,[],[f39])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (19549)------------------------------
% 0.20/0.50  % (19549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (19549)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (19549)Memory used [KB]: 6652
% 0.20/0.50  % (19549)Time elapsed: 0.088 s
% 0.20/0.50  % (19549)------------------------------
% 0.20/0.50  % (19549)------------------------------
% 0.20/0.50  % (19522)Success in time 0.142 s
%------------------------------------------------------------------------------
