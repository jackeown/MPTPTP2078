%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 204 expanded)
%              Number of leaves         :   25 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  420 (1013 expanded)
%              Number of equality atoms :  123 ( 358 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f89,f107,f134,f141,f158,f174,f204,f215])).

fof(f215,plain,
    ( spl6_15
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f212,f202,f132,f139])).

fof(f139,plain,
    ( spl6_15
  <=> sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f132,plain,
    ( spl6_14
  <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f202,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f212,plain,
    ( sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(resolution,[],[f207,f133])).

fof(f133,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK0))
        | k1_funct_1(sK1,X1) = X1 )
    | ~ spl6_25 ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,
    ( ! [X1] :
        ( k1_funct_1(sK1,X1) = X1
        | ~ r2_hidden(X1,k2_relat_1(sK0))
        | ~ r2_hidden(X1,k2_relat_1(sK0)) )
    | ~ spl6_25 ),
    inference(resolution,[],[f203,f55])).

fof(f55,plain,(
    ! [X0,X5] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK5(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f202])).

fof(f204,plain,
    ( ~ spl6_7
    | ~ spl6_6
    | spl6_25
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f199,f172,f105,f202,f78,f82])).

fof(f82,plain,
    ( spl6_7
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f78,plain,
    ( spl6_6
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f105,plain,
    ( spl6_11
  <=> ! [X3,X2] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f172,plain,
    ( spl6_19
  <=> ! [X1] :
        ( k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))
        | ~ r2_hidden(X1,k1_relat_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK0))
        | ~ r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | ~ v1_funct_1(sK0)
        | ~ v1_relat_1(sK0) )
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(resolution,[],[f175,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f175,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0),k1_relat_1(sK0))
        | k1_funct_1(sK1,X0) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(superposition,[],[f173,f109])).

fof(f109,plain,
    ( ! [X0] :
        ( k1_funct_1(sK0,sK5(sK0,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK0)) )
    | ~ spl6_11 ),
    inference(resolution,[],[f106,f55])).

fof(f106,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3 )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f105])).

fof(f173,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))
        | ~ r2_hidden(X1,k1_relat_1(sK0)) )
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( ~ spl6_7
    | spl6_19
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f170,f156,f78,f62,f172,f82])).

fof(f62,plain,
    ( spl6_2
  <=> sK0 = k5_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f156,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f170,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))
        | ~ v1_relat_1(sK0)
        | ~ r2_hidden(X1,k1_relat_1(sK0)) )
    | ~ spl6_2
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f164,f63])).

fof(f63,plain,
    ( sK0 = k5_relat_1(sK0,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f164,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(sK0)
        | ~ r2_hidden(X1,k1_relat_1(sK0))
        | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) )
    | ~ spl6_6
    | ~ spl6_16 ),
    inference(resolution,[],[f157,f79])).

fof(f79,plain,
    ( v1_funct_1(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f78])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( ~ spl6_5
    | spl6_16
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f153,f70,f156,f74])).

fof(f74,plain,
    ( spl6_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f70,plain,
    ( spl6_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(X1))
        | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f42,f71])).

fof(f71,plain,
    ( v1_funct_1(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f70])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

fof(f141,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | spl6_8
    | ~ spl6_15
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f137,f66,f139,f87,f70,f74])).

fof(f87,plain,
    ( spl6_8
  <=> sK1 = k6_relat_1(k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f66,plain,
    ( spl6_3
  <=> k2_relat_1(sK0) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f137,plain,
    ( sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(superposition,[],[f50,f67])).

fof(f67,plain,
    ( k2_relat_1(sK0) = k1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f50,plain,(
    ! [X1] :
      ( sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
            & r2_hidden(sK2(X0,X1),X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X1,X2) != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1))
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X3] :
                ( k1_funct_1(X1,X3) = X3
                | ~ r2_hidden(X3,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2] :
              ( k1_funct_1(X1,X2) != X2
              & r2_hidden(X2,X0) )
          | k1_relat_1(X1) != X0 )
        & ( ( ! [X2] :
                ( k1_funct_1(X1,X2) = X2
                | ~ r2_hidden(X2,X0) )
            & k1_relat_1(X1) = X0 )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( k1_funct_1(X1,X2) = X2
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0 ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k6_relat_1(X0) = X1
      <=> ( ! [X2] :
              ( r2_hidden(X2,X0)
             => k1_funct_1(X1,X2) = X2 )
          & k1_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).

fof(f134,plain,
    ( ~ spl6_5
    | ~ spl6_4
    | spl6_8
    | spl6_14
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f129,f66,f132,f87,f70,f74])).

fof(f129,plain,
    ( r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))
    | sK1 = k6_relat_1(k2_relat_1(sK0))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl6_3 ),
    inference(superposition,[],[f51,f67])).

fof(f51,plain,(
    ! [X1] :
      ( r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1))
      | k6_relat_1(k1_relat_1(X1)) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | k1_relat_1(X1) != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f107,plain,
    ( ~ spl6_7
    | spl6_11
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f98,f78,f105,f82])).

fof(f98,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK0)
        | k1_funct_1(sK0,X2) = X3
        | ~ v1_relat_1(sK0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f48,f79])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f89,plain,
    ( ~ spl6_8
    | spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f85,f66,f58,f87])).

fof(f58,plain,
    ( spl6_1
  <=> sK1 = k6_relat_1(k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( sK1 != k6_relat_1(k2_relat_1(sK0))
    | spl6_1
    | ~ spl6_3 ),
    inference(forward_demodulation,[],[f59,f67])).

fof(f59,plain,
    ( sK1 != k6_relat_1(k1_relat_1(sK1))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f84,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f31,f82])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK1 != k6_relat_1(k1_relat_1(sK1))
    & sK0 = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X1)) != X1
            & k5_relat_1(X0,X1) = X0
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & sK0 = k5_relat_1(sK0,X1)
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k6_relat_1(k1_relat_1(X1)) != X1
        & sK0 = k5_relat_1(sK0,X1)
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( sK1 != k6_relat_1(k1_relat_1(sK1))
      & sK0 = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k6_relat_1(k1_relat_1(X1)) != X1
          & k5_relat_1(X0,X1) = X0
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k5_relat_1(X0,X1) = X0
                & k2_relat_1(X0) = k1_relat_1(X1) )
             => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

fof(f80,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f33,f74])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    sK0 = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f37,f58])).

fof(f37,plain,(
    sK1 != k6_relat_1(k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:23:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (16081)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.45  % (16081)Refutation not found, incomplete strategy% (16081)------------------------------
% 0.22/0.45  % (16081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (16081)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (16081)Memory used [KB]: 10618
% 0.22/0.45  % (16081)Time elapsed: 0.033 s
% 0.22/0.45  % (16081)------------------------------
% 0.22/0.45  % (16081)------------------------------
% 0.22/0.47  % (16086)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (16086)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f216,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f60,f64,f68,f72,f76,f80,f84,f89,f107,f134,f141,f158,f174,f204,f215])).
% 0.22/0.48  fof(f215,plain,(
% 0.22/0.48    spl6_15 | ~spl6_14 | ~spl6_25),
% 0.22/0.48    inference(avatar_split_clause,[],[f212,f202,f132,f139])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    spl6_15 <=> sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    spl6_14 <=> r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.48  fof(f202,plain,(
% 0.22/0.48    spl6_25 <=> ! [X1,X0] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0) | ~r2_hidden(X0,k2_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.48  fof(f212,plain,(
% 0.22/0.48    sK2(k2_relat_1(sK0),sK1) = k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) | (~spl6_14 | ~spl6_25)),
% 0.22/0.48    inference(resolution,[],[f207,f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | ~spl6_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f132])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    ( ! [X1] : (~r2_hidden(X1,k2_relat_1(sK0)) | k1_funct_1(sK1,X1) = X1) ) | ~spl6_25),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f206])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    ( ! [X1] : (k1_funct_1(sK1,X1) = X1 | ~r2_hidden(X1,k2_relat_1(sK0)) | ~r2_hidden(X1,k2_relat_1(sK0))) ) | ~spl6_25),
% 0.22/0.48    inference(resolution,[],[f203,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0,X5] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,k2_relat_1(X0))) )),
% 0.22/0.48    inference(equality_resolution,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK5(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f24,f27,f26,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK3(X0,X1)),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK3(X0,X1)),X0) => r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK5(X0,X5),X5),X0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(rectify,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.22/0.48  fof(f203,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k2_relat_1(sK0))) ) | ~spl6_25),
% 0.22/0.48    inference(avatar_component_clause,[],[f202])).
% 0.22/0.48  fof(f204,plain,(
% 0.22/0.48    ~spl6_7 | ~spl6_6 | spl6_25 | ~spl6_11 | ~spl6_19),
% 0.22/0.48    inference(avatar_split_clause,[],[f199,f172,f105,f202,f78,f82])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    spl6_7 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl6_6 <=> v1_funct_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl6_11 <=> ! [X3,X2] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.48  fof(f172,plain,(
% 0.22/0.48    spl6_19 <=> ! [X1] : (k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) | ~r2_hidden(X1,k1_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.48  fof(f199,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k2_relat_1(sK0)) | ~r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) ) | (~spl6_11 | ~spl6_19)),
% 0.22/0.48    inference(resolution,[],[f175,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.48  fof(f175,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(sK5(sK0,X0),k1_relat_1(sK0)) | k1_funct_1(sK1,X0) = X0 | ~r2_hidden(X0,k2_relat_1(sK0))) ) | (~spl6_11 | ~spl6_19)),
% 0.22/0.48    inference(superposition,[],[f173,f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ( ! [X0] : (k1_funct_1(sK0,sK5(sK0,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK0))) ) | ~spl6_11),
% 0.22/0.48    inference(resolution,[],[f106,f55])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3) ) | ~spl6_11),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f173,plain,(
% 0.22/0.48    ( ! [X1] : (k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) | ~r2_hidden(X1,k1_relat_1(sK0))) ) | ~spl6_19),
% 0.22/0.48    inference(avatar_component_clause,[],[f172])).
% 0.22/0.48  fof(f174,plain,(
% 0.22/0.48    ~spl6_7 | spl6_19 | ~spl6_2 | ~spl6_6 | ~spl6_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f170,f156,f78,f62,f172,f82])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl6_2 <=> sK0 = k5_relat_1(sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl6_16 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.48  fof(f170,plain,(
% 0.22/0.48    ( ! [X1] : (k1_funct_1(sK0,X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1)) | ~v1_relat_1(sK0) | ~r2_hidden(X1,k1_relat_1(sK0))) ) | (~spl6_2 | ~spl6_6 | ~spl6_16)),
% 0.22/0.48    inference(forward_demodulation,[],[f164,f63])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    sK0 = k5_relat_1(sK0,sK1) | ~spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f164,plain,(
% 0.22/0.48    ( ! [X1] : (~v1_relat_1(sK0) | ~r2_hidden(X1,k1_relat_1(sK0)) | k1_funct_1(k5_relat_1(sK0,sK1),X1) = k1_funct_1(sK1,k1_funct_1(sK0,X1))) ) | (~spl6_6 | ~spl6_16)),
% 0.22/0.48    inference(resolution,[],[f157,f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    v1_funct_1(sK0) | ~spl6_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f157,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0))) ) | ~spl6_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f156])).
% 0.22/0.48  fof(f158,plain,(
% 0.22/0.48    ~spl6_5 | spl6_16 | ~spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f153,f70,f156,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    spl6_5 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    spl6_4 <=> v1_funct_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,sK1),X0) = k1_funct_1(sK1,k1_funct_1(X1,X0)) | ~v1_relat_1(sK1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl6_4),
% 0.22/0.48    inference(resolution,[],[f42,f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    v1_funct_1(sK1) | ~spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f70])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    ~spl6_5 | ~spl6_4 | spl6_8 | ~spl6_15 | ~spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f137,f66,f139,f87,f70,f74])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    spl6_8 <=> sK1 = k6_relat_1(k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    spl6_3 <=> k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    sK2(k2_relat_1(sK0),sK1) != k1_funct_1(sK1,sK2(k2_relat_1(sK0),sK1)) | sK1 = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_3),
% 0.22/0.48    inference(superposition,[],[f50,f67])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(sK1) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f66])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    ( ! [X1] : (sK2(k1_relat_1(X1),X1) != k1_funct_1(X1,sK2(k1_relat_1(X1),X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != k1_funct_1(X1,sK2(X0,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X3] : (k1_funct_1(X1,X3) = X3 | ~r2_hidden(X3,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(rectify,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (((k6_relat_1(X0) = X1 | (? [X2] : (k1_funct_1(X1,X2) != X2 & r2_hidden(X2,X0)) | k1_relat_1(X1) != X0)) & ((! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0) | k6_relat_1(X0) != X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> (! [X2] : (k1_funct_1(X1,X2) = X2 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k6_relat_1(X0) = X1 <=> (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = X2) & k1_relat_1(X1) = X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_funct_1)).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    ~spl6_5 | ~spl6_4 | spl6_8 | spl6_14 | ~spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f129,f66,f132,f87,f70,f74])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    r2_hidden(sK2(k2_relat_1(sK0),sK1),k2_relat_1(sK0)) | sK1 = k6_relat_1(k2_relat_1(sK0)) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~spl6_3),
% 0.22/0.48    inference(superposition,[],[f51,f67])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ( ! [X1] : (r2_hidden(sK2(k1_relat_1(X1),X1),k1_relat_1(X1)) | k6_relat_1(k1_relat_1(X1)) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | k1_relat_1(X1) != X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~spl6_7 | spl6_11 | ~spl6_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f98,f78,f105,f82])).
% 0.22/0.48  fof(f98,plain,(
% 0.22/0.48    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK0) | k1_funct_1(sK0,X2) = X3 | ~v1_relat_1(sK0)) ) | ~spl6_6),
% 0.22/0.48    inference(resolution,[],[f48,f79])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f30])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ~spl6_8 | spl6_1 | ~spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f85,f66,f58,f87])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl6_1 <=> sK1 = k6_relat_1(k1_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    sK1 != k6_relat_1(k2_relat_1(sK0)) | (spl6_1 | ~spl6_3)),
% 0.22/0.48    inference(forward_demodulation,[],[f59,f67])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    sK1 != k6_relat_1(k1_relat_1(sK1)) | spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    spl6_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f31,f82])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    v1_relat_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    (sK1 != k6_relat_1(k1_relat_1(sK1)) & sK0 = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK0 = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & sK0 = k5_relat_1(sK0,X1) & k1_relat_1(X1) = k2_relat_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (sK1 != k6_relat_1(k1_relat_1(sK1)) & sK0 = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (k6_relat_1(k1_relat_1(X1)) != X1 & k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((k6_relat_1(k1_relat_1(X1)) != X1 & (k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl6_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f78])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    v1_funct_1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    spl6_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f33,f74])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f70])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    v1_funct_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl6_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f66])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f36,f62])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    sK0 = k5_relat_1(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    ~spl6_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f37,f58])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    sK1 != k6_relat_1(k1_relat_1(sK1))),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (16086)------------------------------
% 0.22/0.48  % (16086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (16086)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (16086)Memory used [KB]: 10746
% 0.22/0.48  % (16086)Time elapsed: 0.065 s
% 0.22/0.48  % (16086)------------------------------
% 0.22/0.48  % (16086)------------------------------
% 0.22/0.48  % (16094)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (16085)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (16092)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (16087)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (16096)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (16091)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (16079)Success in time 0.137 s
%------------------------------------------------------------------------------
