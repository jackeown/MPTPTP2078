%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 278 expanded)
%              Number of leaves         :   28 ( 116 expanded)
%              Depth                    :   17
%              Number of atoms          :  643 (1585 expanded)
%              Number of equality atoms :  111 ( 378 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f594,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f140,f141,f142,f143,f144,f193,f199,f230,f308,f545,f591,f593])).

fof(f593,plain,
    ( spl11_2
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f550,f227,f196,f190,f82,f86])).

fof(f86,plain,
    ( spl11_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f82,plain,
    ( spl11_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f190,plain,
    ( spl11_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f196,plain,
    ( spl11_11
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f227,plain,
    ( spl11_13
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).

fof(f550,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f198,f514])).

fof(f514,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | v1_funct_2(sK2,sK0,X0) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f513,f262])).

fof(f262,plain,
    ( ! [X11] :
        ( r2_hidden(sK7(sK0,X11,sK2),sK0)
        | v1_funct_2(sK2,sK0,X11) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f261,f192])).

fof(f192,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f190])).

fof(f261,plain,
    ( ! [X11] :
        ( r2_hidden(sK7(sK0,X11,sK2),sK0)
        | v1_funct_2(sK2,sK0,X11)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f241,f83])).

fof(f83,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f82])).

fof(f241,plain,
    ( ! [X11] :
        ( r2_hidden(sK7(sK0,X11,sK2),sK0)
        | v1_funct_2(sK2,sK0,X11)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_13 ),
    inference(superposition,[],[f69,f229])).

fof(f229,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl11_13 ),
    inference(avatar_component_clause,[],[f227])).

fof(f69,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ( ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
        & r2_hidden(sK7(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f513,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK0,X0,sK2),sK0)
        | v1_funct_2(sK2,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(forward_demodulation,[],[f512,f229])).

fof(f512,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2)) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f511,f192])).

fof(f511,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f508,f83])).

fof(f508,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,sK0,X0)
        | ~ r1_tarski(k2_relat_1(sK2),X0)
        | ~ r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(resolution,[],[f311,f63])).

fof(f63,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).

fof(f17,plain,(
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK3(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X0,sK2)),X1)
        | v1_funct_2(sK2,sK0,X0)
        | ~ r1_tarski(X1,X0) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(resolution,[],[f260,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f260,plain,
    ( ! [X9] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9)
        | v1_funct_2(sK2,sK0,X9) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f259,f192])).

fof(f259,plain,
    ( ! [X9] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9)
        | v1_funct_2(sK2,sK0,X9)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f239,f83])).

fof(f239,plain,
    ( ! [X9] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9)
        | v1_funct_2(sK2,sK0,X9)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_13 ),
    inference(superposition,[],[f68,f229])).

fof(f68,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_relat_1(X2),X1)
      | ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f198,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f196])).

fof(f591,plain,
    ( ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | spl11_18 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13
    | ~ spl11_14
    | spl11_18 ),
    inference(subsumption_resolution,[],[f589,f303])).

fof(f303,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),sK0)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl11_14
  <=> r2_hidden(sK7(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f589,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),sK0)
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13
    | spl11_18 ),
    inference(forward_demodulation,[],[f588,f229])).

fof(f588,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ spl11_1
    | ~ spl11_10
    | spl11_18 ),
    inference(subsumption_resolution,[],[f587,f192])).

fof(f587,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl11_1
    | spl11_18 ),
    inference(subsumption_resolution,[],[f579,f83])).

fof(f579,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl11_18 ),
    inference(resolution,[],[f379,f63])).

fof(f379,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2))
    | spl11_18 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl11_18
  <=> r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f545,plain,
    ( ~ spl11_18
    | ~ spl11_1
    | spl11_3
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f541,f227,f196,f190,f90,f82,f377])).

fof(f90,plain,
    ( spl11_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f541,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2))
    | ~ spl11_1
    | spl11_3
    | ~ spl11_10
    | ~ spl11_11
    | ~ spl11_13 ),
    inference(unit_resulting_resolution,[],[f198,f92,f343])).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X0,sK2)),X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
        | ~ r1_tarski(X1,X0) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(resolution,[],[f254,f41])).

fof(f254,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f253,f192])).

fof(f253,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f236,f83])).

fof(f236,plain,
    ( ! [X6] :
        ( ~ r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_13 ),
    inference(superposition,[],[f66,f229])).

fof(f66,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f308,plain,
    ( spl11_14
    | ~ spl11_1
    | spl11_3
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(avatar_split_clause,[],[f306,f227,f190,f90,f82,f301])).

fof(f306,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),sK0)
    | ~ spl11_1
    | spl11_3
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(resolution,[],[f256,f92])).

fof(f256,plain,
    ( ! [X7] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | r2_hidden(sK7(sK0,X7,sK2),sK0) )
    | ~ spl11_1
    | ~ spl11_10
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f255,f192])).

fof(f255,plain,
    ( ! [X7] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | r2_hidden(sK7(sK0,X7,sK2),sK0)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_1
    | ~ spl11_13 ),
    inference(subsumption_resolution,[],[f237,f83])).

fof(f237,plain,
    ( ! [X7] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7)))
        | r2_hidden(sK7(sK0,X7,sK2),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl11_13 ),
    inference(superposition,[],[f67,f229])).

fof(f67,plain,(
    ! [X2,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))
      | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK7(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f230,plain,
    ( spl11_13
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f225,f126,f121,f227])).

fof(f121,plain,
    ( spl11_6
  <=> sK0 = k1_relat_1(sK10(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f126,plain,
    ( spl11_7
  <=> sK2 = sK10(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f225,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl11_6
    | ~ spl11_7 ),
    inference(forward_demodulation,[],[f123,f128])).

fof(f128,plain,
    ( sK2 = sK10(sK0,sK1,sK2)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f123,plain,
    ( sK0 = k1_relat_1(sK10(sK0,sK1,sK2))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f199,plain,
    ( spl11_11
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(avatar_split_clause,[],[f194,f126,f95,f196])).

fof(f95,plain,
    ( spl11_4
  <=> r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f194,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl11_4
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f188,f97])).

fof(f97,plain,
    ( r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f188,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ r2_hidden(sK2,k1_funct_2(sK0,sK1))
    | ~ spl11_7 ),
    inference(superposition,[],[f76,f128])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1)
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | sK8(X0,X1,X2) != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X1)
              & k1_relat_1(sK9(X0,X1,X2)) = X0
              & sK8(X0,X1,X2) = sK9(X0,X1,X2)
              & v1_funct_1(sK9(X0,X1,X2))
              & v1_relat_1(sK9(X0,X1,X2)) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1)
                & k1_relat_1(sK10(X0,X1,X6)) = X0
                & sK10(X0,X1,X6) = X6
                & v1_funct_1(sK10(X0,X1,X6))
                & v1_relat_1(sK10(X0,X1,X6)) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f28,f31,f30,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r1_tarski(k2_relat_1(X4),X1)
                | k1_relat_1(X4) != X0
                | X3 != X4
                | ~ v1_funct_1(X4)
                | ~ v1_relat_1(X4) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r1_tarski(k2_relat_1(X5),X1)
                & k1_relat_1(X5) = X0
                & X3 = X5
                & v1_funct_1(X5)
                & v1_relat_1(X5) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r1_tarski(k2_relat_1(X4),X1)
              | k1_relat_1(X4) != X0
              | sK8(X0,X1,X2) != X4
              | ~ v1_funct_1(X4)
              | ~ v1_relat_1(X4) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r1_tarski(k2_relat_1(X5),X1)
              & k1_relat_1(X5) = X0
              & sK8(X0,X1,X2) = X5
              & v1_funct_1(X5)
              & v1_relat_1(X5) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r1_tarski(k2_relat_1(X5),X1)
          & k1_relat_1(X5) = X0
          & sK8(X0,X1,X2) = X5
          & v1_funct_1(X5)
          & v1_relat_1(X5) )
     => ( r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X1)
        & k1_relat_1(sK9(X0,X1,X2)) = X0
        & sK8(X0,X1,X2) = sK9(X0,X1,X2)
        & v1_funct_1(sK9(X0,X1,X2))
        & v1_relat_1(sK9(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r1_tarski(k2_relat_1(X8),X1)
          & k1_relat_1(X8) = X0
          & X6 = X8
          & v1_funct_1(X8)
          & v1_relat_1(X8) )
     => ( r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1)
        & k1_relat_1(sK10(X0,X1,X6)) = X0
        & sK10(X0,X1,X6) = X6
        & v1_funct_1(sK10(X0,X1,X6))
        & v1_relat_1(sK10(X0,X1,X6)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r1_tarski(k2_relat_1(X5),X1)
                  & k1_relat_1(X5) = X0
                  & X3 = X5
                  & v1_funct_1(X5)
                  & v1_relat_1(X5) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r1_tarski(k2_relat_1(X7),X1)
                  | k1_relat_1(X7) != X0
                  | X6 != X7
                  | ~ v1_funct_1(X7)
                  | ~ v1_relat_1(X7) ) )
            & ( ? [X8] :
                  ( r1_tarski(k2_relat_1(X8),X1)
                  & k1_relat_1(X8) = X0
                  & X6 = X8
                  & v1_funct_1(X8)
                  & v1_relat_1(X8) )
              | ~ r2_hidden(X6,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_funct_2(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r1_tarski(k2_relat_1(X4),X1)
                  | k1_relat_1(X4) != X0
                  | X3 != X4
                  | ~ v1_funct_1(X4)
                  | ~ v1_relat_1(X4) ) )
            & ( ? [X4] :
                  ( r1_tarski(k2_relat_1(X4),X1)
                  & k1_relat_1(X4) = X0
                  & X3 = X4
                  & v1_funct_1(X4)
                  & v1_relat_1(X4) )
              | ~ r2_hidden(X3,X2) ) )
        | k1_funct_2(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k1_funct_2(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r1_tarski(k2_relat_1(X4),X1)
              & k1_relat_1(X4) = X0
              & X3 = X4
              & v1_funct_1(X4)
              & v1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

fof(f193,plain,
    ( spl11_10
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f183,f136,f126,f190])).

fof(f136,plain,
    ( spl11_9
  <=> v1_relat_1(sK10(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f183,plain,
    ( v1_relat_1(sK2)
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(backward_demodulation,[],[f138,f128])).

fof(f138,plain,
    ( v1_relat_1(sK10(sK0,sK1,sK2))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f144,plain,
    ( sK2 != sK10(sK0,sK1,sK2)
    | v1_funct_1(sK2)
    | ~ v1_funct_1(sK10(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f143,plain,
    ( spl11_6
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f107,f95,f121])).

fof(f107,plain,
    ( sK0 = k1_relat_1(sK10(sK0,sK1,sK2))
    | ~ spl11_4 ),
    inference(resolution,[],[f97,f77])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( k1_relat_1(sK10(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_relat_1(sK10(X0,X1,X6)) = X0
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f142,plain,
    ( spl11_7
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f106,f95,f126])).

fof(f106,plain,
    ( sK2 = sK10(sK0,sK1,sK2)
    | ~ spl11_4 ),
    inference(resolution,[],[f97,f78])).

fof(f78,plain,(
    ! [X6,X0,X1] :
      ( sK10(X0,X1,X6) = X6
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( sK10(X0,X1,X6) = X6
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f141,plain,
    ( spl11_8
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f105,f95,f131])).

fof(f131,plain,
    ( spl11_8
  <=> v1_funct_1(sK10(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f105,plain,
    ( v1_funct_1(sK10(sK0,sK1,sK2))
    | ~ spl11_4 ),
    inference(resolution,[],[f97,f79])).

fof(f79,plain,(
    ! [X6,X0,X1] :
      ( v1_funct_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_funct_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f140,plain,
    ( spl11_9
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f104,f95,f136])).

fof(f104,plain,
    ( v1_relat_1(sK10(sK0,sK1,sK2))
    | ~ spl11_4 ),
    inference(resolution,[],[f97,f80])).

fof(f80,plain,(
    ! [X6,X0,X1] :
      ( v1_relat_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,k1_funct_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X6,X2,X0,X1] :
      ( v1_relat_1(sK10(X0,X1,X6))
      | ~ r2_hidden(X6,X2)
      | k1_funct_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f33,f95])).

fof(f33,plain,(
    r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & r2_hidden(X2,k1_funct_2(X0,X1)) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & r2_hidden(sK2,k1_funct_2(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

fof(f93,plain,
    ( ~ spl11_1
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f34,f90,f86,f82])).

fof(f34,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (14911)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.48  % (14911)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (14903)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f594,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f93,f98,f140,f141,f142,f143,f144,f193,f199,f230,f308,f545,f591,f593])).
% 0.21/0.49  fof(f593,plain,(
% 0.21/0.49    spl11_2 | ~spl11_1 | ~spl11_10 | ~spl11_11 | ~spl11_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f550,f227,f196,f190,f82,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl11_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl11_1 <=> v1_funct_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.49  fof(f190,plain,(
% 0.21/0.49    spl11_10 <=> v1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    spl11_11 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).
% 0.21/0.49  fof(f227,plain,(
% 0.21/0.49    spl11_13 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl11_13])])).
% 0.21/0.49  fof(f550,plain,(
% 0.21/0.49    v1_funct_2(sK2,sK0,sK1) | (~spl11_1 | ~spl11_10 | ~spl11_11 | ~spl11_13)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f198,f514])).
% 0.21/0.49  fof(f514,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,sK0,X0)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f513,f262])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    ( ! [X11] : (r2_hidden(sK7(sK0,X11,sK2),sK0) | v1_funct_2(sK2,sK0,X11)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f261,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    v1_relat_1(sK2) | ~spl11_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f190])).
% 0.21/0.49  fof(f261,plain,(
% 0.21/0.49    ( ! [X11] : (r2_hidden(sK7(sK0,X11,sK2),sK0) | v1_funct_2(sK2,sK0,X11) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_13)),
% 0.21/0.49    inference(subsumption_resolution,[],[f241,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    v1_funct_1(sK2) | ~spl11_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    ( ! [X11] : (r2_hidden(sK7(sK0,X11,sK2),sK0) | v1_funct_2(sK2,sK0,X11) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl11_13),
% 0.21/0.49    inference(superposition,[],[f69,f229])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    sK0 = k1_relat_1(sK2) | ~spl11_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f227])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(equality_resolution,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | r2_hidden(sK7(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f12,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) & r2_hidden(sK7(X0,X1,X2),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.50    inference(flattening,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.50  fof(f513,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(sK7(sK0,X0,sK2),sK0) | v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(forward_demodulation,[],[f512,f229])).
% 0.21/0.50  fof(f512,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2))) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f511,f192])).
% 0.21/0.50  fof(f511,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f508,f83])).
% 0.21/0.50  fof(f508,plain,(
% 0.21/0.50    ( ! [X0] : (v1_funct_2(sK2,sK0,X0) | ~r1_tarski(k2_relat_1(sK2),X0) | ~r2_hidden(sK7(sK0,X0,sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(resolution,[],[f311,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f16,f19,f18,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK3(X0,X1) = k1_funct_1(X0,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(rectify,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f8])).
% 0.21/0.50  fof(f8,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X0,sK2)),X1) | v1_funct_2(sK2,sK0,X0) | ~r1_tarski(X1,X0)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(resolution,[],[f260,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f22,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(rectify,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(nnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ( ! [X9] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9) | v1_funct_2(sK2,sK0,X9)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f192])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ( ! [X9] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9) | v1_funct_2(sK2,sK0,X9) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f239,f83])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    ( ! [X9] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X9,sK2)),X9) | v1_funct_2(sK2,sK0,X9) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl11_13),
% 0.21/0.50    inference(superposition,[],[f68,f229])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X1] : (v1_funct_2(X2,k1_relat_1(X2),X1) | ~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~spl11_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f196])).
% 0.21/0.50  fof(f591,plain,(
% 0.21/0.50    ~spl11_1 | ~spl11_10 | ~spl11_13 | ~spl11_14 | spl11_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f590])).
% 0.21/0.50  fof(f590,plain,(
% 0.21/0.50    $false | (~spl11_1 | ~spl11_10 | ~spl11_13 | ~spl11_14 | spl11_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f589,f303])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    r2_hidden(sK7(sK0,sK1,sK2),sK0) | ~spl11_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f301])).
% 0.21/0.50  fof(f301,plain,(
% 0.21/0.50    spl11_14 <=> r2_hidden(sK7(sK0,sK1,sK2),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 0.21/0.50  fof(f589,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK0,sK1,sK2),sK0) | (~spl11_1 | ~spl11_10 | ~spl11_13 | spl11_18)),
% 0.21/0.50    inference(forward_demodulation,[],[f588,f229])).
% 0.21/0.50  fof(f588,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2)) | (~spl11_1 | ~spl11_10 | spl11_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f587,f192])).
% 0.21/0.50  fof(f587,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl11_1 | spl11_18)),
% 0.21/0.50    inference(subsumption_resolution,[],[f579,f83])).
% 0.21/0.50  fof(f579,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK0,sK1,sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl11_18),
% 0.21/0.50    inference(resolution,[],[f379,f63])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2)) | spl11_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f377])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    spl11_18 <=> r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    ~spl11_18 | ~spl11_1 | spl11_3 | ~spl11_10 | ~spl11_11 | ~spl11_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f541,f227,f196,f190,f90,f82,f377])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl11_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.50  fof(f541,plain,(
% 0.21/0.50    ~r2_hidden(k1_funct_1(sK2,sK7(sK0,sK1,sK2)),k2_relat_1(sK2)) | (~spl11_1 | spl11_3 | ~spl11_10 | ~spl11_11 | ~spl11_13)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f198,f92,f343])).
% 0.21/0.50  fof(f343,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X0,sK2)),X1) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) | ~r1_tarski(X1,X0)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(resolution,[],[f254,f41])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X6] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f192])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X6] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f236,f83])).
% 0.21/0.50  fof(f236,plain,(
% 0.21/0.50    ( ! [X6] : (~r2_hidden(k1_funct_1(sK2,sK7(sK0,X6,sK2)),X6) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl11_13),
% 0.21/0.50    inference(superposition,[],[f66,f229])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | ~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl11_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f308,plain,(
% 0.21/0.50    spl11_14 | ~spl11_1 | spl11_3 | ~spl11_10 | ~spl11_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f306,f227,f190,f90,f82,f301])).
% 0.21/0.50  fof(f306,plain,(
% 0.21/0.50    r2_hidden(sK7(sK0,sK1,sK2),sK0) | (~spl11_1 | spl11_3 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(resolution,[],[f256,f92])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ( ! [X7] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | r2_hidden(sK7(sK0,X7,sK2),sK0)) ) | (~spl11_1 | ~spl11_10 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f255,f192])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X7] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | r2_hidden(sK7(sK0,X7,sK2),sK0) | ~v1_relat_1(sK2)) ) | (~spl11_1 | ~spl11_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f237,f83])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    ( ! [X7] : (m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X7))) | r2_hidden(sK7(sK0,X7,sK2),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl11_13),
% 0.21/0.50    inference(superposition,[],[f67,f229])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK7(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    spl11_13 | ~spl11_6 | ~spl11_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f225,f126,f121,f227])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl11_6 <=> sK0 = k1_relat_1(sK10(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl11_7 <=> sK2 = sK10(sK0,sK1,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.21/0.50  fof(f225,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK2) | (~spl11_6 | ~spl11_7)),
% 0.21/0.50    inference(forward_demodulation,[],[f123,f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    sK2 = sK10(sK0,sK1,sK2) | ~spl11_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f126])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK10(sK0,sK1,sK2)) | ~spl11_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f121])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl11_11 | ~spl11_4 | ~spl11_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f194,f126,f95,f196])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl11_4 <=> r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | (~spl11_4 | ~spl11_7)),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f97])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl11_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f95])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    r1_tarski(k2_relat_1(sK2),sK1) | ~r2_hidden(sK2,k1_funct_2(sK0,sK1)) | ~spl11_7),
% 0.21/0.50    inference(superposition,[],[f76,f128])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK8(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X1) & k1_relat_1(sK9(X0,X1,X2)) = X0 & sK8(X0,X1,X2) = sK9(X0,X1,X2) & v1_funct_1(sK9(X0,X1,X2)) & v1_relat_1(sK9(X0,X1,X2))) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & ((r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1) & k1_relat_1(sK10(X0,X1,X6)) = X0 & sK10(X0,X1,X6) = X6 & v1_funct_1(sK10(X0,X1,X6)) & v1_relat_1(sK10(X0,X1,X6))) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f28,f31,f30,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2))) => ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | sK8(X0,X1,X2) != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK8(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & sK8(X0,X1,X2) = X5 & v1_funct_1(X5) & v1_relat_1(X5)) => (r1_tarski(k2_relat_1(sK9(X0,X1,X2)),X1) & k1_relat_1(sK9(X0,X1,X2)) = X0 & sK8(X0,X1,X2) = sK9(X0,X1,X2) & v1_funct_1(sK9(X0,X1,X2)) & v1_relat_1(sK9(X0,X1,X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X6,X1,X0] : (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) => (r1_tarski(k2_relat_1(sK10(X0,X1,X6)),X1) & k1_relat_1(sK10(X0,X1,X6)) = X0 & sK10(X0,X1,X6) = X6 & v1_funct_1(sK10(X0,X1,X6)) & v1_relat_1(sK10(X0,X1,X6))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X5] : (r1_tarski(k2_relat_1(X5),X1) & k1_relat_1(X5) = X0 & X3 = X5 & v1_funct_1(X5) & v1_relat_1(X5)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r1_tarski(k2_relat_1(X7),X1) | k1_relat_1(X7) != X0 | X6 != X7 | ~v1_funct_1(X7) | ~v1_relat_1(X7))) & (? [X8] : (r1_tarski(k2_relat_1(X8),X1) & k1_relat_1(X8) = X0 & X6 = X8 & v1_funct_1(X8) & v1_relat_1(X8)) | ~r2_hidden(X6,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k1_funct_2(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4)) | ~r2_hidden(X3,X2)) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r1_tarski(k2_relat_1(X4),X1) | k1_relat_1(X4) != X0 | X3 != X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4))) & (? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4)) | ~r2_hidden(X3,X2))) | k1_funct_2(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k1_funct_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r1_tarski(k2_relat_1(X4),X1) & k1_relat_1(X4) = X0 & X3 = X4 & v1_funct_1(X4) & v1_relat_1(X4))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    spl11_10 | ~spl11_7 | ~spl11_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f183,f136,f126,f190])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    spl11_9 <=> v1_relat_1(sK10(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    v1_relat_1(sK2) | (~spl11_7 | ~spl11_9)),
% 0.21/0.50    inference(backward_demodulation,[],[f138,f128])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    v1_relat_1(sK10(sK0,sK1,sK2)) | ~spl11_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f136])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    sK2 != sK10(sK0,sK1,sK2) | v1_funct_1(sK2) | ~v1_funct_1(sK10(sK0,sK1,sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl11_6 | ~spl11_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f107,f95,f121])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    sK0 = k1_relat_1(sK10(sK0,sK1,sK2)) | ~spl11_4),
% 0.21/0.50    inference(resolution,[],[f97,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (k1_relat_1(sK10(X0,X1,X6)) = X0 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (k1_relat_1(sK10(X0,X1,X6)) = X0 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    spl11_7 | ~spl11_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f106,f95,f126])).
% 0.21/0.50  fof(f106,plain,(
% 0.21/0.50    sK2 = sK10(sK0,sK1,sK2) | ~spl11_4),
% 0.21/0.50    inference(resolution,[],[f97,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (sK10(X0,X1,X6) = X6 | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (sK10(X0,X1,X6) = X6 | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    spl11_8 | ~spl11_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f95,f131])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl11_8 <=> v1_funct_1(sK10(sK0,sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    v1_funct_1(sK10(sK0,sK1,sK2)) | ~spl11_4),
% 0.21/0.50    inference(resolution,[],[f97,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (v1_funct_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (v1_funct_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl11_9 | ~spl11_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f95,f136])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    v1_relat_1(sK10(sK0,sK1,sK2)) | ~spl11_4),
% 0.21/0.50    inference(resolution,[],[f97,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X6,X0,X1] : (v1_relat_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,k1_funct_2(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (v1_relat_1(sK10(X0,X1,X6)) | ~r2_hidden(X6,X2) | k1_funct_2(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl11_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f33,f95])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1))) => ((~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) & r2_hidden(sK2,k1_funct_2(sK0,sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) & r2_hidden(X2,k1_funct_2(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ~spl11_1 | ~spl11_2 | ~spl11_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f90,f86,f82])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (14911)------------------------------
% 0.21/0.50  % (14911)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14911)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (14911)Memory used [KB]: 6652
% 0.21/0.50  % (14911)Time elapsed: 0.078 s
% 0.21/0.50  % (14911)------------------------------
% 0.21/0.50  % (14911)------------------------------
% 0.21/0.50  % (14885)Success in time 0.144 s
%------------------------------------------------------------------------------
