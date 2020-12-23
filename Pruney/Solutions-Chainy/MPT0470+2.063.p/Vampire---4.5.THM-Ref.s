%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 122 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  241 ( 459 expanded)
%              Number of equality atoms :   57 ( 133 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f54,f114,f168,f220])).

fof(f220,plain,
    ( spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f218,f52,f48,f44])).

fof(f44,plain,
    ( spl5_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f48,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f52,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f218,plain,
    ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f213,f49])).

fof(f49,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f213,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k1_xboole_0 = k5_relat_1(X3,k1_xboole_0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f211,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f31,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f211,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(X0,k1_xboole_0,k1_xboole_0),sK2(X0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f204,f53])).

fof(f53,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f204,plain,
    ( ! [X2,X1] :
        ( ~ v1_xboole_0(X2)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK3(X1,X2,k1_xboole_0),sK2(X1,X2,k1_xboole_0)),X2)
        | k1_xboole_0 = k5_relat_1(X1,X2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f198,f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f198,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X5)
        | k1_xboole_0 = k5_relat_1(X4,X5)
        | ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK3(X4,X5,k1_xboole_0),sK2(X4,X5,k1_xboole_0)),X5) )
    | ~ spl5_4 ),
    inference(resolution,[],[f139,f55])).

fof(f139,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f68,f53])).

fof(f68,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_xboole_0(X4)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3) ) ),
    inference(resolution,[],[f29,f24])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f17,f16,f15])).

fof(f15,plain,(
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

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1)
          & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0) )
     => ( r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X8,X7,X1,X0] :
      ( ? [X10] :
          ( r2_hidden(k4_tarski(X10,X8),X1)
          & r2_hidden(k4_tarski(X7,X10),X0) )
     => ( r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1)
        & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f168,plain,(
    ~ spl5_12 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | ~ spl5_12 ),
    inference(resolution,[],[f113,f55])).

fof(f113,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_12
  <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f114,plain,
    ( spl5_1
    | spl5_12
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f109,f52,f48,f112,f41])).

fof(f41,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f109,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f90,f53])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0)
        | k1_xboole_0 = k5_relat_1(X0,sK0) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f87,f24])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(X0,sK0)
        | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f76,f49])).

fof(f76,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X5)
        | k1_xboole_0 = k5_relat_1(X4,X5)
        | ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK1(X4,X5,k1_xboole_0),sK3(X4,X5,k1_xboole_0)),X4) )
    | ~ spl5_4 ),
    inference(resolution,[],[f74,f55])).

fof(f74,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f60,f53])).

fof(f60,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_xboole_0(X4)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2) ) ),
    inference(resolution,[],[f28,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f23,f52])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f50,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f46,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f22,f44,f41])).

fof(f22,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:11:23 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.41  % (5954)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.41  % (5954)Refutation not found, incomplete strategy% (5954)------------------------------
% 0.19/0.41  % (5954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (5954)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.41  
% 0.19/0.41  % (5954)Memory used [KB]: 6140
% 0.19/0.41  % (5954)Time elapsed: 0.007 s
% 0.19/0.41  % (5954)------------------------------
% 0.19/0.41  % (5954)------------------------------
% 0.19/0.41  % (5944)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.42  % (5944)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f221,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f46,f50,f54,f114,f168,f220])).
% 0.19/0.42  fof(f220,plain,(
% 0.19/0.42    spl5_2 | ~spl5_3 | ~spl5_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f218,f52,f48,f44])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl5_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    spl5_3 <=> v1_relat_1(sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.42  fof(f52,plain,(
% 0.19/0.42    spl5_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.42  fof(f218,plain,(
% 0.19/0.42    k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | (~spl5_3 | ~spl5_4)),
% 0.19/0.42    inference(resolution,[],[f213,f49])).
% 0.19/0.42  fof(f49,plain,(
% 0.19/0.42    v1_relat_1(sK0) | ~spl5_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f48])).
% 0.19/0.42  fof(f213,plain,(
% 0.19/0.42    ( ! [X3] : (~v1_relat_1(X3) | k1_xboole_0 = k5_relat_1(X3,k1_xboole_0)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f211,f55])).
% 0.19/0.42  fof(f55,plain,(
% 0.19/0.42    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(superposition,[],[f31,f38])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.19/0.42    inference(equality_resolution,[],[f34])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.19/0.42    inference(cnf_transformation,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.42    inference(flattening,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.19/0.42    inference(nnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.19/0.42  fof(f211,plain,(
% 0.19/0.42    ( ! [X0] : (r2_hidden(k4_tarski(sK3(X0,k1_xboole_0,k1_xboole_0),sK2(X0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f204,f53])).
% 0.19/0.42  fof(f53,plain,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0) | ~spl5_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f52])).
% 0.19/0.42  fof(f204,plain,(
% 0.19/0.42    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK3(X1,X2,k1_xboole_0),sK2(X1,X2,k1_xboole_0)),X2) | k1_xboole_0 = k5_relat_1(X1,X2)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f198,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.19/0.42  fof(f198,plain,(
% 0.19/0.42    ( ! [X4,X5] : (~v1_relat_1(X5) | k1_xboole_0 = k5_relat_1(X4,X5) | ~v1_relat_1(X4) | r2_hidden(k4_tarski(sK3(X4,X5,k1_xboole_0),sK2(X4,X5,k1_xboole_0)),X5)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f139,f55])).
% 0.19/0.42  fof(f139,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f68,f53])).
% 0.19/0.42  fof(f68,plain,(
% 0.19/0.42    ( ! [X4,X2,X3] : (~v1_xboole_0(X4) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3)) )),
% 0.19/0.42    inference(resolution,[],[f29,f24])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f14,f17,f16,f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(rectify,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(nnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.19/0.42  fof(f168,plain,(
% 0.19/0.42    ~spl5_12),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f167])).
% 0.19/0.42  fof(f167,plain,(
% 0.19/0.42    $false | ~spl5_12),
% 0.19/0.42    inference(resolution,[],[f113,f55])).
% 0.19/0.42  fof(f113,plain,(
% 0.19/0.42    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | ~spl5_12),
% 0.19/0.42    inference(avatar_component_clause,[],[f112])).
% 0.19/0.42  fof(f112,plain,(
% 0.19/0.42    spl5_12 <=> r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    spl5_1 | spl5_12 | ~spl5_3 | ~spl5_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f109,f52,f48,f112,f41])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    spl5_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl5_3 | ~spl5_4)),
% 0.19/0.42    inference(resolution,[],[f90,f53])).
% 0.19/0.42  fof(f90,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_xboole_0(X0) | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0) | k1_xboole_0 = k5_relat_1(X0,sK0)) ) | (~spl5_3 | ~spl5_4)),
% 0.19/0.42    inference(resolution,[],[f87,f24])).
% 0.19/0.42  fof(f87,plain,(
% 0.19/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,sK0) | r2_hidden(k4_tarski(sK1(X0,sK0,k1_xboole_0),sK3(X0,sK0,k1_xboole_0)),X0)) ) | (~spl5_3 | ~spl5_4)),
% 0.19/0.42    inference(resolution,[],[f76,f49])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    ( ! [X4,X5] : (~v1_relat_1(X5) | k1_xboole_0 = k5_relat_1(X4,X5) | ~v1_relat_1(X4) | r2_hidden(k4_tarski(sK1(X4,X5,k1_xboole_0),sK3(X4,X5,k1_xboole_0)),X4)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f74,f55])).
% 0.19/0.42  fof(f74,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0)) ) | ~spl5_4),
% 0.19/0.42    inference(resolution,[],[f60,f53])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    ( ! [X4,X2,X3] : (~v1_xboole_0(X4) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2)) )),
% 0.19/0.42    inference(resolution,[],[f28,f24])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f18])).
% 0.19/0.42  fof(f54,plain,(
% 0.19/0.42    spl5_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f23,f52])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    v1_xboole_0(k1_xboole_0)),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    spl5_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f21,f48])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    v1_relat_1(sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f8,plain,(
% 0.19/0.42    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.19/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    ~spl5_1 | ~spl5_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f22,f44,f41])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (5944)------------------------------
% 0.19/0.42  % (5944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (5944)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (5944)Memory used [KB]: 10746
% 0.19/0.42  % (5944)Time elapsed: 0.008 s
% 0.19/0.42  % (5944)------------------------------
% 0.19/0.42  % (5944)------------------------------
% 0.19/0.42  % (5936)Success in time 0.077 s
%------------------------------------------------------------------------------
