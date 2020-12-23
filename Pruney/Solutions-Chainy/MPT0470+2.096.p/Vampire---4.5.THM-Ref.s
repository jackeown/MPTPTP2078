%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 161 expanded)
%              Number of leaves         :   19 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  328 ( 611 expanded)
%              Number of equality atoms :   67 ( 149 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f82,f85,f162,f172,f191,f220,f223])).

fof(f223,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | ~ spl5_21 ),
    inference(resolution,[],[f218,f55])).

fof(f55,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f34,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f218,plain,
    ( r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl5_21
  <=> r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f220,plain,
    ( spl5_21
    | spl5_6
    | spl5_2
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f215,f189,f52,f48,f77,f217])).

fof(f77,plain,
    ( spl5_6
  <=> ! [X2] : ~ v1_relat_1(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f48,plain,
    ( spl5_2
  <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f52,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f189,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f215,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
        | ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) )
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f214,f26])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f214,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_relat_1(sK0,X0)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0) )
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f202,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0)
        | k1_xboole_0 = k5_relat_1(sK0,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f199,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f199,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(sK0,X0)
        | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0) )
    | ~ spl5_3
    | ~ spl5_17 ),
    inference(resolution,[],[f194,f53])).

fof(f53,plain,
    ( v1_relat_1(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f194,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK3(X4,X5,k1_xboole_0),sK2(X4,X5,k1_xboole_0)),X5)
        | k1_xboole_0 = k5_relat_1(X4,X5)
        | ~ v1_relat_1(X5) )
    | ~ spl5_17 ),
    inference(resolution,[],[f190,f55])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl5_6
    | spl5_17 ),
    inference(avatar_split_clause,[],[f187,f189,f77])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f123,f26])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1)
      | ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ),
    inference(resolution,[],[f68,f35])).

fof(f68,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3)
      | ~ v1_relat_1(X5) ) ),
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

% (11451)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
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

% (11431)Refutation not found, incomplete strategy% (11431)------------------------------
% (11431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11431)Termination reason: Refutation not found, incomplete strategy

% (11431)Memory used [KB]: 10618
% (11431)Time elapsed: 0.089 s
% (11431)------------------------------
% (11431)------------------------------
% (11433)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

fof(f172,plain,
    ( spl5_1
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f169,f160,f52,f45])).

fof(f45,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f160,plain,
    ( spl5_14
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f169,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(resolution,[],[f164,f53])).

fof(f164,plain,
    ( ! [X3] :
        ( ~ v1_relat_1(X3)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X3) )
    | ~ spl5_14 ),
    inference(resolution,[],[f161,f55])).

fof(f161,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl5_6
    | spl5_14
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f158,f80,f160,f77])).

fof(f80,plain,
    ( spl5_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0)
        | ~ v1_relat_1(X1)
        | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
    | ~ spl5_7 ),
    inference(resolution,[],[f157,f26])).

fof(f157,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X2)
        | ~ v1_relat_1(X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0)
        | ~ v1_relat_1(X2)
        | k1_xboole_0 = k5_relat_1(X0,X1) )
    | ~ spl5_7 ),
    inference(resolution,[],[f150,f35])).

fof(f150,plain,
    ( ! [X2,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X3))
        | k1_xboole_0 = k5_relat_1(X1,X2)
        | ~ v1_relat_1(X2)
        | r2_hidden(k4_tarski(sK1(X1,X2,k1_xboole_0),sK3(X1,X2,k1_xboole_0)),X1)
        | ~ v1_relat_1(X3) )
    | ~ spl5_7 ),
    inference(resolution,[],[f125,f33])).

% (11451)Refutation not found, incomplete strategy% (11451)------------------------------
% (11451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (11451)Termination reason: Refutation not found, incomplete strategy

% (11451)Memory used [KB]: 10618
% (11451)Time elapsed: 0.092 s
fof(f125,plain,
    ( ! [X4,X5] :
        ( ~ v1_relat_1(X4)
        | r2_hidden(k4_tarski(sK1(X4,X5,k1_xboole_0),sK3(X4,X5,k1_xboole_0)),X4)
        | k1_xboole_0 = k5_relat_1(X4,X5)
        | ~ v1_relat_1(X5) )
    | ~ spl5_7 ),
    inference(resolution,[],[f81,f55])).

% (11451)------------------------------
% (11451)------------------------------
fof(f81,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f80])).

fof(f85,plain,
    ( ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f53,f78])).

fof(f78,plain,
    ( ! [X2] : ~ v1_relat_1(X2)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f82,plain,
    ( spl5_6
    | spl5_7 ),
    inference(avatar_split_clause,[],[f75,f80,f77])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f74,f26])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,X3)
      | k5_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ v1_relat_1(X3)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) ) ),
    inference(resolution,[],[f60,f35])).

fof(f60,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X5))
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4)
      | k5_relat_1(X2,X3) = X4
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2)
      | ~ v1_relat_1(X5) ) ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

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
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:56:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (11435)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (11445)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (11436)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (11437)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (11430)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (11434)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (11430)Refutation not found, incomplete strategy% (11430)------------------------------
% 0.21/0.51  % (11430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (11430)Memory used [KB]: 6140
% 0.21/0.51  % (11430)Time elapsed: 0.079 s
% 0.21/0.51  % (11430)------------------------------
% 0.21/0.51  % (11430)------------------------------
% 0.21/0.51  % (11432)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (11449)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (11431)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11436)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f50,f54,f82,f85,f162,f172,f191,f220,f223])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ~spl5_21),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f222])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    $false | ~spl5_21),
% 0.21/0.52    inference(resolution,[],[f218,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f34,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0) | ~spl5_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f217])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    spl5_21 <=> r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.52  fof(f220,plain,(
% 0.21/0.52    spl5_21 | spl5_6 | spl5_2 | ~spl5_3 | ~spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f215,f189,f52,f48,f77,f217])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    spl5_6 <=> ! [X2] : ~v1_relat_1(X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl5_2 <=> k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    spl5_3 <=> v1_relat_1(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f189,plain,(
% 0.21/0.52    spl5_17 <=> ! [X1,X0] : (k1_xboole_0 = k5_relat_1(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,k1_xboole_0),sK2(sK0,k1_xboole_0,k1_xboole_0)),k1_xboole_0)) ) | (~spl5_3 | ~spl5_17)),
% 0.21/0.52    inference(resolution,[],[f214,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_relat_1(sK0,X0) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0)) ) | (~spl5_3 | ~spl5_17)),
% 0.21/0.52    inference(resolution,[],[f202,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0) | k1_xboole_0 = k5_relat_1(sK0,X0) | ~v1_relat_1(X1)) ) | (~spl5_3 | ~spl5_17)),
% 0.21/0.52    inference(resolution,[],[f199,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(sK0,X0) | r2_hidden(k4_tarski(sK3(sK0,X0,k1_xboole_0),sK2(sK0,X0,k1_xboole_0)),X0)) ) | (~spl5_3 | ~spl5_17)),
% 0.21/0.52    inference(resolution,[],[f194,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    v1_relat_1(sK0) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f52])).
% 0.21/0.52  fof(f194,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~v1_relat_1(X4) | r2_hidden(k4_tarski(sK3(X4,X5,k1_xboole_0),sK2(X4,X5,k1_xboole_0)),X5) | k1_xboole_0 = k5_relat_1(X4,X5) | ~v1_relat_1(X5)) ) | ~spl5_17),
% 0.21/0.52    inference(resolution,[],[f190,f55])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,X1) | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) ) | ~spl5_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f189])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    spl5_6 | spl5_17),
% 0.21/0.52    inference(avatar_split_clause,[],[f187,f189,f77])).
% 0.21/0.52  fof(f187,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f123,f26])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) )),
% 0.21/0.52    inference(resolution,[],[f68,f35])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X2,X3,X4),sK2(X2,X3,X4)),X3) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(resolution,[],[f31,f33])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & ((r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f20,f19,f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2))) => ((! [X5] : (~r2_hidden(k4_tarski(X5,sK2(X0,X1,X2)),X1) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),X5),X0)) | ~r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (11451)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X6] : (r2_hidden(k4_tarski(X6,sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X6),X0)) => (r2_hidden(k4_tarski(sK3(X0,X1,X2),sK2(X0,X1,X2)),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X8,X7,X1,X0] : (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) => (r2_hidden(k4_tarski(sK4(X0,X1,X7,X8),X8),X1) & r2_hidden(k4_tarski(X7,sK4(X0,X1,X7,X8)),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  % (11431)Refutation not found, incomplete strategy% (11431)------------------------------
% 0.21/0.52  % (11431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11431)Memory used [KB]: 10618
% 0.21/0.52  % (11431)Time elapsed: 0.089 s
% 0.21/0.52  % (11431)------------------------------
% 0.21/0.52  % (11431)------------------------------
% 0.21/0.52  % (11433)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X6] : (r2_hidden(k4_tarski(X6,X4),X1) & r2_hidden(k4_tarski(X3,X6),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X7,X8] : ((r2_hidden(k4_tarski(X7,X8),X2) | ! [X9] : (~r2_hidden(k4_tarski(X9,X8),X1) | ~r2_hidden(k4_tarski(X7,X9),X0))) & (? [X10] : (r2_hidden(k4_tarski(X10,X8),X1) & r2_hidden(k4_tarski(X7,X10),X0)) | ~r2_hidden(k4_tarski(X7,X8),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(rectify,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (((k5_relat_1(X0,X1) = X2 | ? [X3,X4] : ((! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2)) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(k4_tarski(X3,X4),X2)))) & (! [X3,X4] : ((r2_hidden(k4_tarski(X3,X4),X2) | ! [X5] : (~r2_hidden(k4_tarski(X5,X4),X1) | ~r2_hidden(k4_tarski(X3,X5),X0))) & (? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)) | ~r2_hidden(k4_tarski(X3,X4),X2))) | k5_relat_1(X0,X1) != X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k5_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> ? [X5] : (r2_hidden(k4_tarski(X5,X4),X1) & r2_hidden(k4_tarski(X3,X5),X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    spl5_1 | ~spl5_3 | ~spl5_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f169,f160,f52,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl5_1 <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    spl5_14 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) | (~spl5_3 | ~spl5_14)),
% 0.21/0.52    inference(resolution,[],[f164,f53])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    ( ! [X3] : (~v1_relat_1(X3) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X3)) ) | ~spl5_14),
% 0.21/0.52    inference(resolution,[],[f161,f55])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | ~spl5_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f160])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    spl5_6 | spl5_14 | ~spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f158,f80,f160,f77])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl5_7 <=> ! [X1,X0] : (k1_xboole_0 = k5_relat_1(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,X0,k1_xboole_0),sK3(k1_xboole_0,X0,k1_xboole_0)),k1_xboole_0) | ~v1_relat_1(X1) | k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f157,f26])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | ~v1_relat_1(X1) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0) | ~v1_relat_1(X2) | k1_xboole_0 = k5_relat_1(X0,X1)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f150,f35])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X3)) | k1_xboole_0 = k5_relat_1(X1,X2) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X1,X2,k1_xboole_0),sK3(X1,X2,k1_xboole_0)),X1) | ~v1_relat_1(X3)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f125,f33])).
% 0.21/0.52  % (11451)Refutation not found, incomplete strategy% (11451)------------------------------
% 0.21/0.52  % (11451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11451)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11451)Memory used [KB]: 10618
% 0.21/0.52  % (11451)Time elapsed: 0.092 s
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~v1_relat_1(X4) | r2_hidden(k4_tarski(sK1(X4,X5,k1_xboole_0),sK3(X4,X5,k1_xboole_0)),X4) | k1_xboole_0 = k5_relat_1(X4,X5) | ~v1_relat_1(X5)) ) | ~spl5_7),
% 0.21/0.52    inference(resolution,[],[f81,f55])).
% 0.21/0.52  % (11451)------------------------------
% 0.21/0.52  % (11451)------------------------------
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0) | k1_xboole_0 = k5_relat_1(X0,X1) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) ) | ~spl5_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f80])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ~spl5_3 | ~spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    $false | (~spl5_3 | ~spl5_6)),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2] : (~v1_relat_1(X2)) ) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f77])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl5_6 | spl5_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f75,f80,f77])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK3(X0,X1,k1_xboole_0)),X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,k1_xboole_0),sK2(X0,X1,k1_xboole_0)),k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f74,f26])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,X3) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~v1_relat_1(X3) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2)) )),
% 0.21/0.52    inference(resolution,[],[f60,f35])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X4,X2,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X5)) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK2(X2,X3,X4)),X4) | k5_relat_1(X2,X3) = X4 | ~v1_relat_1(X3) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X2,X3,X4),sK3(X2,X3,X4)),X2) | ~v1_relat_1(X5)) )),
% 0.21/0.52    inference(resolution,[],[f30,f33])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK2(X0,X1,X2)),X2) | k5_relat_1(X0,X1) = X2 | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    v1_relat_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f7])).
% 0.21/0.52  fof(f7,conjecture,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ~spl5_1 | ~spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f25,f48,f45])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11436)------------------------------
% 0.21/0.52  % (11436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11436)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11436)Memory used [KB]: 10746
% 0.21/0.52  % (11436)Time elapsed: 0.026 s
% 0.21/0.52  % (11436)------------------------------
% 0.21/0.52  % (11436)------------------------------
% 0.21/0.52  % (11433)Refutation not found, incomplete strategy% (11433)------------------------------
% 0.21/0.52  % (11433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11433)Memory used [KB]: 10618
% 0.21/0.52  % (11433)Time elapsed: 0.087 s
% 0.21/0.52  % (11433)------------------------------
% 0.21/0.52  % (11433)------------------------------
% 0.21/0.52  % (11427)Success in time 0.155 s
%------------------------------------------------------------------------------
