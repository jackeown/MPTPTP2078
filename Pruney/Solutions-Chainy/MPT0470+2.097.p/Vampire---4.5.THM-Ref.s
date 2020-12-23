%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 132 expanded)
%              Number of leaves         :   15 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 ( 507 expanded)
%              Number of equality atoms :   60 ( 136 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f151,f210,f213,f224])).

fof(f224,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl5_12 ),
    inference(resolution,[],[f150,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f150,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_12
  <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f213,plain,(
    ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | ~ spl5_16 ),
    inference(resolution,[],[f209,f55])).

fof(f209,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_16
  <=> r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f210,plain,
    ( spl5_2
    | spl5_16
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f204,f52,f208,f48])).

fof(f48,plain,
    ( spl5_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f52,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f204,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl5_3 ),
    inference(resolution,[],[f199,f26])).

fof(f26,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f199,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK3(sK0,X3,k1_xboole_0),sK2(sK0,X3,k1_xboole_0)),X3)
        | k1_xboole_0 = k5_relat_1(sK0,X3) )
    | ~ spl5_3 ),
    inference(resolution,[],[f196,f55])).

fof(f196,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k1_xboole_0 = k5_relat_1(sK0,X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f194,f26])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | k5_relat_1(sK0,X0) = X1
        | r2_hidden(k4_tarski(sK3(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f192,f53])).

fof(f53,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f192,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k5_relat_1(sK0,X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK3(sK0,X0,X1),sK2(sK0,X0,X1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f173,f53])).

fof(f173,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
        | k5_relat_1(X2,X3) = X4
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(X5))
        | ~ v1_relat_1(X5) )
    | ~ spl5_3 ),
    inference(resolution,[],[f128,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(X0,X1) = X2
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3) ) ),
    inference(resolution,[],[f31,f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ( ( ! [X5] :
                          ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
                          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
                      | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
                    & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
                        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) )
                      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
                          & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ! [X5] :
                ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                | ~ r2_hidden(k4_tarski(X3,X5),X0) )
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ? [X6] :
                ( r2_hidden(k4_tarski(X6,X4),X1)
                & r2_hidden(k4_tarski(X3,X6),X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ! [X5] :
              ( ~ r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1)
              | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0) )
          | ~ r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) )
        & ( ? [X6] :
              ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
              & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
          | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X6] :
                            ( r2_hidden(k4_tarski(X6,X4),X1)
                            & r2_hidden(k4_tarski(X3,X6),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X7,X8] :
                      ( ( r2_hidden(k4_tarski(X7,X8),X2)
                        | ! [X9] :
                            ( ~ r2_hidden(k4_tarski(X9,X8),X1)
                            | ~ r2_hidden(k4_tarski(X7,X9),X0) ) )
                      & ( ? [X10] :
                            ( r2_hidden(k4_tarski(X10,X8),X1)
                            & r2_hidden(k4_tarski(X7,X10),X0) )
                        | ~ r2_hidden(k4_tarski(X7,X8),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k5_relat_1(X0,X1) = X2
                  | ? [X3,X4] :
                      ( ( ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
                & ( ! [X3,X4] :
                      ( ( r2_hidden(k4_tarski(X3,X4),X2)
                        | ! [X5] :
                            ( ~ r2_hidden(k4_tarski(X5,X4),X1)
                            | ~ r2_hidden(k4_tarski(X3,X5),X0) ) )
                      & ( ? [X5] :
                            ( r2_hidden(k4_tarski(X5,X4),X1)
                            & r2_hidden(k4_tarski(X3,X5),X0) )
                        | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
                  | k5_relat_1(X0,X1) != X2 ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).

fof(f151,plain,
    ( spl5_1
    | spl5_12
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f145,f52,f149,f45])).

fof(f45,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f145,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f119,f26])).

fof(f119,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(X3,sK0,k1_xboole_0),sK3(X3,sK0,k1_xboole_0)),X3)
        | k1_xboole_0 = k5_relat_1(X3,sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f116,f55])).

fof(f116,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK2(X0,sK0,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k1_xboole_0 = k5_relat_1(X0,sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f114,f26])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | k5_relat_1(X0,sK0) = X1
        | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK3(X0,sK0,X1)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f79,f53])).

fof(f79,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X3)
        | k5_relat_1(X1,sK0) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK3(X1,sK0,X2)),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
        | r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK2(X1,sK0,X2)),X2) )
    | ~ spl5_3 ),
    inference(resolution,[],[f76,f33])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1)
        | k5_relat_1(X0,sK0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK3(X0,sK0,X1)),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f74,f53])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X1)
        | k5_relat_1(X0,X1) = X2
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
        | ~ v1_relat_1(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f60,f53])).

fof(f60,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v1_relat_1(X5)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2) ) ),
    inference(resolution,[],[f30,f33])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f50,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f25,f48,f45])).

fof(f25,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n022.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 15:26:56 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.14/0.41  % (7264)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.44  % (7262)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.45  % (7254)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.47  % (7251)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.47  % (7253)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.47  % (7254)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f229,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f50,f54,f151,f210,f213,f224])).
% 0.19/0.47  fof(f224,plain,(
% 0.19/0.47    ~spl5_12),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f223])).
% 0.19/0.47  fof(f223,plain,(
% 0.19/0.47    $false | ~spl5_12),
% 0.19/0.47    inference(resolution,[],[f150,f55])).
% 0.19/0.47  fof(f55,plain,(
% 0.19/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.47    inference(superposition,[],[f34,f42])).
% 0.19/0.47  fof(f42,plain,(
% 0.19/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.47    inference(equality_resolution,[],[f37])).
% 0.19/0.47  fof(f37,plain,(
% 0.19/0.47    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f23])).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.47    inference(flattening,[],[f22])).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.19/0.47    inference(nnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f2])).
% 0.19/0.47  fof(f2,axiom,(
% 0.19/0.47    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.19/0.47  fof(f150,plain,(
% 0.19/0.47    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | ~spl5_12),
% 0.19/0.47    inference(avatar_component_clause,[],[f149])).
% 0.19/0.47  fof(f149,plain,(
% 0.19/0.47    spl5_12 <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.47  fof(f213,plain,(
% 0.19/0.47    ~spl5_16),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f212])).
% 0.19/0.47  fof(f212,plain,(
% 0.19/0.47    $false | ~spl5_16),
% 0.19/0.47    inference(resolution,[],[f209,f55])).
% 0.19/0.47  fof(f209,plain,(
% 0.19/0.47    r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_16),
% 0.19/0.47    inference(avatar_component_clause,[],[f208])).
% 0.19/0.47  fof(f208,plain,(
% 0.19/0.47    spl5_16 <=> r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.19/0.47  fof(f210,plain,(
% 0.19/0.47    spl5_2 | spl5_16 | ~spl5_3),
% 0.19/0.47    inference(avatar_split_clause,[],[f204,f52,f208,f48])).
% 0.19/0.47  fof(f48,plain,(
% 0.19/0.47    spl5_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.47  fof(f52,plain,(
% 0.19/0.47    spl5_3 <=> v1_relat_1(sK0)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.47  fof(f204,plain,(
% 0.19/0.47    r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f199,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f3])).
% 0.19/0.47  fof(f3,axiom,(
% 0.19/0.47    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.19/0.47  fof(f199,plain,(
% 0.19/0.47    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X3,k1_xboole_0),sK2(sK0,X3,k1_xboole_0)),X3) | k1_xboole_0 = k5_relat_1(sK0,X3)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f196,f55])).
% 0.19/0.47  fof(f196,plain,(
% 0.19/0.47    ( ! [X0] : (r2_hidden(k4_tarski(sK1(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k1_xboole_0 = k5_relat_1(sK0,X0)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f194,f26])).
% 0.19/0.47  fof(f194,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k5_relat_1(sK0,X0) = X1 | r2_hidden(k4_tarski(sK3(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f192,f53])).
% 0.19/0.47  fof(f53,plain,(
% 0.19/0.47    v1_relat_1(sK0) | ~spl5_3),
% 0.19/0.47    inference(avatar_component_clause,[],[f52])).
% 0.19/0.47  fof(f192,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(sK0,X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK3(sK0,X0,X1),sK2(sK0,X0,X1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(k4_tarski(sK1(sK0,X0,X1),sK2(sK0,X0,X1)),X1)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f173,f53])).
% 0.19/0.47  fof(f173,plain,(
% 0.19/0.47    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X5)) | ~v1_relat_1(X5)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f128,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f11])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.47  fof(f128,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)) ) | ~spl5_3),
% 0.19/0.47    inference(resolution,[],[f68,f53])).
% 0.19/0.47  fof(f68,plain,(
% 0.19/0.47    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3)) )),
% 0.19/0.47    inference(resolution,[],[f31,f33])).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.47    inference(cnf_transformation,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(rectify,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_1)).
% 0.19/0.48  fof(f151,plain,(
% 0.19/0.48    spl5_1 | spl5_12 | ~spl5_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f145,f52,f149,f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    spl5_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.48  fof(f145,plain,(
% 0.19/0.48    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f119,f26])).
% 0.19/0.48  fof(f119,plain,(
% 0.19/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(X3,sK0,k1_xboole_0),sK3(X3,sK0,k1_xboole_0)),X3) | k1_xboole_0 = k5_relat_1(X3,sK0)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f116,f55])).
% 0.19/0.48  fof(f116,plain,(
% 0.19/0.48    ( ! [X0] : (r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK2(X0,sK0,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k1_xboole_0 = k5_relat_1(X0,sK0)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f114,f26])).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | k5_relat_1(X0,sK0) = X1 | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK3(X0,sK0,X1)),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f79,f53])).
% 0.19/0.48  fof(f79,plain,(
% 0.19/0.48    ( ! [X2,X3,X1] : (~v1_relat_1(X3) | k5_relat_1(X1,sK0) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK3(X1,sK0,X2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X3)) | r2_hidden(k4_tarski(sK1(X1,sK0,X2),sK2(X1,sK0,X2)),X2)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f76,f33])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK2(X0,sK0,X1)),X1) | k5_relat_1(X0,sK0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(X0,sK0,X1),sK3(X0,sK0,X1)),X0)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f74,f53])).
% 0.19/0.48  fof(f74,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | ~v1_relat_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(sK0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) ) | ~spl5_3),
% 0.19/0.48    inference(resolution,[],[f60,f53])).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ( ! [X4,X2,X5,X3] : (~v1_relat_1(X5) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2)) )),
% 0.19/0.48    inference(resolution,[],[f30,f33])).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f21])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    spl5_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f24,f52])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    v1_relat_1(sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,negated_conjecture,(
% 0.19/0.48    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.48    inference(negated_conjecture,[],[f7])).
% 0.19/0.48  fof(f7,conjecture,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    ~spl5_1 | ~spl5_2),
% 0.19/0.48    inference(avatar_split_clause,[],[f25,f48,f45])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (7254)------------------------------
% 0.19/0.48  % (7254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7254)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (7254)Memory used [KB]: 10874
% 0.19/0.48  % (7254)Time elapsed: 0.029 s
% 0.19/0.48  % (7254)------------------------------
% 0.19/0.48  % (7254)------------------------------
% 0.19/0.48  % (7267)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.19/0.48  % (7247)Success in time 0.146 s
%------------------------------------------------------------------------------
