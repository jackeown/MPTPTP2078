%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t5_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:47 EDT 2019

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  254 (1177 expanded)
%              Number of leaves         :   42 ( 331 expanded)
%              Depth                    :   21
%              Number of atoms          :  803 (5117 expanded)
%              Number of equality atoms :  129 ( 796 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f131,f461,f977,f1071,f1145,f1190,f8223,f31075,f40705,f43705,f54724,f55663,f55696,f55893,f56255,f73103,f75573])).

fof(f75573,plain,
    ( spl8_371
    | ~ spl8_1184 ),
    inference(avatar_contradiction_clause,[],[f75572])).

fof(f75572,plain,
    ( $false
    | ~ spl8_371
    | ~ spl8_1184 ),
    inference(subsumption_resolution,[],[f75563,f12201])).

fof(f12201,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl8_371 ),
    inference(avatar_component_clause,[],[f12200])).

fof(f12200,plain,
    ( spl8_371
  <=> ~ m1_subset_1(k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_371])])).

fof(f75563,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl8_371
    | ~ spl8_1184 ),
    inference(resolution,[],[f75549,f73538])).

fof(f73538,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | m1_subset_1(X0,k1_xboole_0) )
    | ~ spl8_1184 ),
    inference(superposition,[],[f88,f40704])).

fof(f40704,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0
    | ~ spl8_1184 ),
    inference(avatar_component_clause,[],[f40703])).

fof(f40703,plain,
    ( spl8_1184
  <=> k1_zfmisc_1(sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1184])])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t3_subset)).

fof(f75549,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1)
    | ~ spl8_371
    | ~ spl8_1184 ),
    inference(resolution,[],[f75536,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f61,f62])).

fof(f62,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',d3_tarski)).

fof(f75536,plain,
    ( r2_hidden(sK7(k2_relat_1(sK2),sK1),sK1)
    | ~ spl8_371
    | ~ spl8_1184 ),
    inference(resolution,[],[f75244,f1482])).

fof(f1482,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_relat_1(sK2))
      | r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f1480,f1035])).

fof(f1035,plain,(
    ! [X0] :
      ( r2_hidden(sK5(sK2,X0),sK0)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f710,f68])).

fof(f68,plain,(
    k1_relat_1(sK2) = sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & ! [X3] :
        ( r2_hidden(k1_funct_1(sK2,X3),sK1)
        | ~ r2_hidden(X3,sK0) )
    & k1_relat_1(sK2) = sK0
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & ! [X3] :
            ( r2_hidden(k1_funct_1(X2,X3),X1)
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(X2) = X0
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(sK2,X3),sK1)
          | ~ r2_hidden(X3,sK0) )
      & k1_relat_1(sK2) = sK0
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & ! [X3] :
          ( r2_hidden(k1_funct_1(X2,X3),X1)
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( ! [X3] :
                ( r2_hidden(X3,X0)
               => r2_hidden(k1_funct_1(X2,X3),X1) )
            & k1_relat_1(X2) = X0 )
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t5_funct_2)).

fof(f710,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f709,f66])).

fof(f66,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f709,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(sK5(sK2,X0),k1_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f105,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f53,f56,f55,f54])).

fof(f54,plain,(
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

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',d5_funct_1)).

fof(f1480,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(sK5(sK2,X1),sK0)
      | ~ r2_hidden(X1,k2_relat_1(sK2)) ) ),
    inference(superposition,[],[f69,f806])).

fof(f806,plain,(
    ! [X0] :
      ( k1_funct_1(sK2,sK5(sK2,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f805,f66])).

fof(f805,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | k1_funct_1(sK2,sK5(sK2,X0)) = X0
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f104,f67])).

fof(f104,plain,(
    ! [X0,X5] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f69,plain,(
    ! [X3] :
      ( r2_hidden(k1_funct_1(sK2,X3),sK1)
      | ~ r2_hidden(X3,sK0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f75244,plain,
    ( r2_hidden(sK7(k2_relat_1(sK2),sK1),k2_relat_1(sK2))
    | ~ spl8_371
    | ~ spl8_1184 ),
    inference(resolution,[],[f74062,f12201])).

fof(f74062,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_xboole_0)
        | r2_hidden(sK7(X0,sK1),X0) )
    | ~ spl8_1184 ),
    inference(resolution,[],[f73538,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f73103,plain,
    ( spl8_5
    | ~ spl8_222
    | ~ spl8_1182 ),
    inference(avatar_contradiction_clause,[],[f73102])).

fof(f73102,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_222
    | ~ spl8_1182 ),
    inference(subsumption_resolution,[],[f73085,f128])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_5
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f73085,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_222
    | ~ spl8_1182 ),
    inference(resolution,[],[f73082,f9765])).

fof(f9765,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(X1))
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
    | ~ spl8_222 ),
    inference(resolution,[],[f9401,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f9401,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(sK2),X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) )
    | ~ spl8_222 ),
    inference(resolution,[],[f1712,f6025])).

fof(f6025,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl8_222 ),
    inference(avatar_component_clause,[],[f6024])).

fof(f6024,plain,
    ( spl8_222
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_222])])).

fof(f1712,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(forward_demodulation,[],[f872,f68])).

fof(f872,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(sK2),X0)
      | ~ r1_tarski(k1_relat_1(sK2),X1)
      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f91,f66])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t11_relset_1)).

fof(f73082,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_1182 ),
    inference(subsumption_resolution,[],[f73071,f64963])).

fof(f64963,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_zfmisc_1(sK1),X0)
        | m1_subset_1(k2_relat_1(sK2),X0) )
    | ~ spl8_1182 ),
    inference(resolution,[],[f56807,f88])).

fof(f56807,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(X1))
        | m1_subset_1(k2_relat_1(sK2),X1) )
    | ~ spl8_1182 ),
    inference(resolution,[],[f40698,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t4_subset)).

fof(f40698,plain,
    ( r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | ~ spl8_1182 ),
    inference(avatar_component_clause,[],[f40697])).

fof(f40697,plain,
    ( spl8_1182
  <=> r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1182])])).

fof(f73071,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(sK1))
    | ~ spl8_1182 ),
    inference(resolution,[],[f64975,f86])).

fof(f64975,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(k1_zfmisc_1(sK1),X0),k1_zfmisc_1(sK1))
        | m1_subset_1(k2_relat_1(sK2),X0) )
    | ~ spl8_1182 ),
    inference(resolution,[],[f64963,f85])).

fof(f56255,plain,
    ( spl8_8
    | spl8_6 ),
    inference(avatar_split_clause,[],[f56249,f144,f147])).

fof(f147,plain,
    ( spl8_8
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f144,plain,
    ( spl8_6
  <=> ! [X1] : ~ r2_hidden(X1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f56249,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f69,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t5_subset)).

fof(f55893,plain,
    ( spl8_46
    | spl8_8 ),
    inference(avatar_split_clause,[],[f36146,f147,f1050])).

fof(f1050,plain,
    ( spl8_46
  <=> ! [X1] : ~ r2_hidden(X1,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f36146,plain,(
    ! [X127,X128] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X127))
      | ~ v1_xboole_0(X127)
      | ~ r2_hidden(X128,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f101,f15484])).

fof(f15484,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f15477,f1470])).

fof(f1470,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(sK1,X6)
      | r2_hidden(k1_funct_1(sK2,sK5(sK2,X7)),X6)
      | ~ r2_hidden(X7,k2_relat_1(sK2)) ) ),
    inference(resolution,[],[f141,f1035])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_tarski(sK1,X1)
      | r2_hidden(k1_funct_1(sK2,X0),X1) ) ),
    inference(resolution,[],[f84,f69])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f15477,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),sK1)
      | r1_tarski(sK1,sK1) ) ),
    inference(resolution,[],[f2412,f86])).

fof(f2412,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(sK1,X1),sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,sK5(sK2,X0)),X1) ) ),
    inference(resolution,[],[f1470,f85])).

fof(f55696,plain,
    ( ~ spl8_5
    | spl8_102
    | spl8_3 ),
    inference(avatar_split_clause,[],[f31233,f121,f2374,f127])).

fof(f2374,plain,
    ( spl8_102
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f121,plain,
    ( spl8_3
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f31233,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f31232,f68])).

fof(f31232,plain,
    ( k1_relat_1(sK2) != sK0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(resolution,[],[f122,f1518])).

fof(f1518,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relat_1(X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f1517])).

fof(f1517,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f96,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',redefinition_k1_relset_1)).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',d1_funct_2)).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f121])).

fof(f55663,plain,
    ( spl8_3
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_102 ),
    inference(avatar_contradiction_clause,[],[f55662])).

fof(f55662,plain,
    ( $false
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_14
    | ~ spl8_18
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f55661,f8931])).

fof(f8931,plain,
    ( ! [X2] : v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f8930,f415])).

fof(f415,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl8_14
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f8930,plain,
    ( ! [X2] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl8_14 ),
    inference(trivial_inequality_removal,[],[f8929])).

fof(f8929,plain,
    ( ! [X2] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X2)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl8_14 ),
    inference(superposition,[],[f1362,f8917])).

fof(f8917,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ spl8_14 ),
    inference(resolution,[],[f8911,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t6_boole)).

fof(f8911,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl8_14 ),
    inference(resolution,[],[f2075,f415])).

fof(f2075,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
      | v1_xboole_0(k1_relat_1(X2)) ) ),
    inference(resolution,[],[f317,f402])).

fof(f402,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f93,f92])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',dt_k1_relset_1)).

fof(f317,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(backward_demodulation,[],[f315,f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f80,f133])).

fof(f133,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f132,f71])).

fof(f71,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',dt_o_0_0_xboole_0)).

fof(f132,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(resolution,[],[f72,f71])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',cc4_relset_1)).

fof(f315,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(subsumption_resolution,[],[f309,f72])).

fof(f309,plain,(
    ! [X0] :
      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0
      | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ) ),
    inference(resolution,[],[f245,f153])).

fof(f153,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X2,k1_xboole_0))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f150,f88])).

fof(f245,plain,(
    ! [X0] :
      ( r1_tarski(k2_zfmisc_1(X0,k1_xboole_0),k2_zfmisc_1(X0,k1_xboole_0))
      | k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[],[f186,f86])).

fof(f186,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK7(X10,k2_zfmisc_1(X11,k1_xboole_0)),X10)
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f159,f72])).

fof(f159,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK7(X0,k2_zfmisc_1(X1,k1_xboole_0)),X0) ) ),
    inference(resolution,[],[f153,f85])).

fof(f1362,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_xboole_0
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(duplicate_literal_removal,[],[f1361])).

fof(f1361,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_xboole_0
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f109,f92])).

fof(f109,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f55661,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_102 ),
    inference(forward_demodulation,[],[f55213,f1201])).

fof(f1201,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_18 ),
    inference(resolution,[],[f457,f191])).

fof(f191,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f187,f88])).

fof(f187,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f170,f133])).

fof(f170,plain,(
    ! [X2,X3] :
      ( ~ v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f165,f101])).

fof(f165,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f16,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',existence_m1_subset_1)).

fof(f140,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | r2_hidden(X6,X7)
      | k1_xboole_0 = X7 ) ),
    inference(resolution,[],[f83,f72])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t2_subset)).

fof(f457,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl8_18
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f55213,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_3
    | ~ spl8_6
    | ~ spl8_102 ),
    inference(backward_demodulation,[],[f2375,f52748])).

fof(f52748,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f175,f122])).

fof(f175,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_6 ),
    inference(resolution,[],[f165,f145])).

fof(f145,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f2375,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f54724,plain,(
    ~ spl8_42 ),
    inference(avatar_contradiction_clause,[],[f54723])).

fof(f54723,plain,
    ( $false
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f54722,f135])).

fof(f135,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f90,f133])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t5_funct_2.p',t7_boole)).

fof(f54722,plain,
    ( r2_hidden(sK6(sK2),k1_xboole_0)
    | ~ spl8_42 ),
    inference(superposition,[],[f976,f315])).

fof(f976,plain,
    ( ! [X54,X53] : r2_hidden(sK6(sK2),k2_zfmisc_1(X53,X54))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f975])).

fof(f975,plain,
    ( spl8_42
  <=> ! [X53,X54] : r2_hidden(sK6(sK2),k2_zfmisc_1(X53,X54)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f43705,plain,
    ( spl8_5
    | ~ spl8_222
    | ~ spl8_370
    | ~ spl8_1184 ),
    inference(avatar_contradiction_clause,[],[f43704])).

fof(f43704,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_222
    | ~ spl8_370
    | ~ spl8_1184 ),
    inference(subsumption_resolution,[],[f41414,f128])).

fof(f41414,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_222
    | ~ spl8_370
    | ~ spl8_1184 ),
    inference(subsumption_resolution,[],[f41317,f12198])).

fof(f12198,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_xboole_0)
    | ~ spl8_370 ),
    inference(avatar_component_clause,[],[f12197])).

fof(f12197,plain,
    ( spl8_370
  <=> m1_subset_1(k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_370])])).

fof(f41317,plain,
    ( ~ m1_subset_1(k2_relat_1(sK2),k1_xboole_0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_222
    | ~ spl8_1184 ),
    inference(superposition,[],[f9765,f40704])).

fof(f40705,plain,
    ( spl8_1182
    | spl8_1184 ),
    inference(avatar_split_clause,[],[f40692,f40703,f40697])).

fof(f40692,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0
    | r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f40684,f167])).

fof(f167,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,X4)
      | k1_zfmisc_1(X4) = k1_xboole_0
      | r2_hidden(X3,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f140,f88])).

fof(f40684,plain,
    ( k1_zfmisc_1(sK1) = k1_xboole_0
    | r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(sK1))
    | r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(resolution,[],[f20447,f86])).

fof(f20447,plain,(
    ! [X67] :
      ( r2_hidden(sK7(k2_relat_1(sK2),X67),sK1)
      | k1_zfmisc_1(X67) = k1_xboole_0
      | r2_hidden(k2_relat_1(sK2),k1_zfmisc_1(X67)) ) ),
    inference(resolution,[],[f257,f1482])).

fof(f257,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X1,X0),X1)
      | r2_hidden(X1,k1_zfmisc_1(X0))
      | k1_zfmisc_1(X0) = k1_xboole_0 ) ),
    inference(resolution,[],[f167,f85])).

fof(f31075,plain,
    ( ~ spl8_8
    | ~ spl8_102 ),
    inference(avatar_contradiction_clause,[],[f31074])).

fof(f31074,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_102 ),
    inference(subsumption_resolution,[],[f30940,f135])).

fof(f30940,plain,
    ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_8
    | ~ spl8_102 ),
    inference(backward_demodulation,[],[f2375,f795])).

fof(f795,plain,
    ( r2_hidden(sK7(sK1,k1_xboole_0),sK1)
    | ~ spl8_8 ),
    inference(resolution,[],[f733,f133])).

fof(f733,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | r2_hidden(sK7(sK1,X0),sK1) )
    | ~ spl8_8 ),
    inference(resolution,[],[f727,f85])).

fof(f727,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_8 ),
    inference(resolution,[],[f148,f88])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f8223,plain,(
    spl8_223 ),
    inference(avatar_contradiction_clause,[],[f8222])).

fof(f8222,plain,
    ( $false
    | ~ spl8_223 ),
    inference(subsumption_resolution,[],[f8214,f6022])).

fof(f6022,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl8_223 ),
    inference(avatar_component_clause,[],[f6021])).

fof(f6021,plain,
    ( spl8_223
  <=> ~ r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_223])])).

fof(f8214,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl8_223 ),
    inference(resolution,[],[f8175,f86])).

fof(f8175,plain,
    ( r2_hidden(sK7(sK0,sK0),sK0)
    | ~ spl8_223 ),
    inference(resolution,[],[f6022,f85])).

fof(f1190,plain,
    ( spl8_28
    | spl8_30 ),
    inference(avatar_split_clause,[],[f1012,f820,f762])).

fof(f762,plain,
    ( spl8_28
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f820,plain,
    ( spl8_30
  <=> r2_hidden(k1_funct_1(sK2,sK6(sK0)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1012,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK0)),k2_relat_1(sK2))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f812,f165])).

fof(f812,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f618,f68])).

fof(f618,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f617,f66])).

fof(f617,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK2))
      | r2_hidden(k1_funct_1(sK2,X0),k2_relat_1(sK2))
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f103,f67])).

fof(f103,plain,(
    ! [X6,X0] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f1145,plain,
    ( spl8_19
    | ~ spl8_38 ),
    inference(avatar_contradiction_clause,[],[f1144])).

fof(f1144,plain,
    ( $false
    | ~ spl8_19
    | ~ spl8_38 ),
    inference(subsumption_resolution,[],[f1142,f135])).

fof(f1142,plain,
    ( r2_hidden(sK7(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_38 ),
    inference(resolution,[],[f1128,f85])).

fof(f1128,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl8_19
    | ~ spl8_38 ),
    inference(backward_demodulation,[],[f968,f460])).

fof(f460,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f459])).

fof(f459,plain,
    ( spl8_19
  <=> ~ r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f968,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl8_38
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1071,plain,
    ( ~ spl8_30
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f1061])).

fof(f1061,plain,
    ( $false
    | ~ spl8_30
    | ~ spl8_46 ),
    inference(resolution,[],[f1051,f821])).

fof(f821,plain,
    ( r2_hidden(k1_funct_1(sK2,sK6(sK0)),k2_relat_1(sK2))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f820])).

fof(f1051,plain,
    ( ! [X1] : ~ r2_hidden(X1,k2_relat_1(sK2))
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f1050])).

fof(f977,plain,
    ( spl8_42
    | spl8_38
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f957,f762,f967,f975])).

fof(f957,plain,
    ( ! [X54,X53] :
        ( k1_xboole_0 = sK2
        | r2_hidden(sK6(sK2),k2_zfmisc_1(X53,X54)) )
    | ~ spl8_28 ),
    inference(resolution,[],[f936,f242])).

fof(f242,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X3))
      | k1_xboole_0 = X2
      | r2_hidden(sK6(X2),X3) ) ),
    inference(resolution,[],[f171,f87])).

fof(f171,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | r2_hidden(sK6(X4),X5)
      | k1_xboole_0 = X4 ) ),
    inference(resolution,[],[f165,f84])).

fof(f936,plain,
    ( ! [X0,X1] : m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f934,f135])).

fof(f934,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | r2_hidden(sK7(k1_xboole_0,X1),k1_xboole_0) )
    | ~ spl8_28 ),
    inference(resolution,[],[f933,f85])).

fof(f933,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f931,f135])).

fof(f931,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | r2_hidden(sK7(k1_xboole_0,X1),k1_xboole_0) )
    | ~ spl8_28 ),
    inference(resolution,[],[f874,f85])).

fof(f874,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | ~ r1_tarski(k1_xboole_0,X0)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f873,f838])).

fof(f838,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | ~ spl8_28 ),
    inference(backward_demodulation,[],[f763,f68])).

fof(f763,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f762])).

fof(f873,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X1)
        | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f872,f842])).

fof(f842,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl8_28 ),
    inference(resolution,[],[f841,f165])).

fof(f841,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_relat_1(sK2))
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f840,f135])).

fof(f840,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK2,X0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl8_28 ),
    inference(forward_demodulation,[],[f710,f838])).

fof(f461,plain,
    ( spl8_14
    | ~ spl8_19
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f454,f144,f459,f414])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k1_xboole_0)
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_6 ),
    inference(superposition,[],[f409,f315])).

fof(f409,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK2,k2_zfmisc_1(X0,X1))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_6 ),
    inference(resolution,[],[f407,f88])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) )
    | ~ spl8_6 ),
    inference(superposition,[],[f402,f180])).

fof(f180,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | ~ spl8_6 ),
    inference(backward_demodulation,[],[f175,f68])).

fof(f131,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f116,f67])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_1
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f129,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f70,f127,f121,f115])).

fof(f70,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
