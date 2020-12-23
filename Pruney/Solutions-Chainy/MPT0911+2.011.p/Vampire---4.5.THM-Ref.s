%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:30 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 252 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  328 (1161 expanded)
%              Number of equality atoms :  156 ( 601 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f180,f263])).

fof(f263,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f261,f55])).

fof(f55,plain,(
    sK4 != k7_mcart_1(sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( sK4 != k7_mcart_1(sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK4 = X7
                | k3_mcart_1(X5,X6,X7) != sK5
                | ~ m1_subset_1(X7,sK3) )
            | ~ m1_subset_1(X6,sK2) )
        | ~ m1_subset_1(X5,sK1) )
    & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK4 != k7_mcart_1(sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK4 = X7
                  | k3_mcart_1(X5,X6,X7) != sK5
                  | ~ m1_subset_1(X7,sK3) )
              | ~ m1_subset_1(X6,sK2) )
          | ~ m1_subset_1(X5,sK1) )
      & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f261,plain,
    ( sK4 = k7_mcart_1(sK1,sK2,sK3,sK5)
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f260,f238])).

fof(f238,plain,
    ( sK4 = k2_mcart_1(sK5)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f237,f187])).

fof(f187,plain,
    ( m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl11_1 ),
    inference(resolution,[],[f183,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f183,plain,
    ( r2_hidden(k2_mcart_1(sK5),sK3)
    | ~ spl11_1 ),
    inference(resolution,[],[f133,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f133,plain,
    ( r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_1
  <=> r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f237,plain,
    ( sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl11_1 ),
    inference(trivial_inequality_removal,[],[f236])).

fof(f236,plain,
    ( sK5 != sK5
    | sK4 = k2_mcart_1(sK5)
    | ~ m1_subset_1(k2_mcart_1(sK5),sK3)
    | ~ spl11_1 ),
    inference(superposition,[],[f235,f211])).

fof(f211,plain,
    ( sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f210,f209])).

fof(f209,plain,
    ( k1_mcart_1(sK5) = sK9(sK5)
    | ~ spl11_1 ),
    inference(superposition,[],[f63,f189])).

fof(f189,plain,
    ( sK5 = k4_tarski(sK9(sK5),sK10(sK5))
    | ~ spl11_1 ),
    inference(resolution,[],[f85,f133])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK9(X0),sK10(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK9(X0),sK10(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f27,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK9(X0),sK10(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

% (11139)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f210,plain,
    ( sK5 = k4_tarski(sK9(sK5),k2_mcart_1(sK5))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f189,f208])).

fof(f208,plain,
    ( k2_mcart_1(sK5) = sK10(sK5)
    | ~ spl11_1 ),
    inference(superposition,[],[f64,f189])).

fof(f64,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f16])).

fof(f235,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = X0
        | ~ m1_subset_1(X0,sK3) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f234,f203])).

fof(f203,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)
    | ~ spl11_1 ),
    inference(resolution,[],[f197,f66])).

fof(f197,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),sK1)
    | ~ spl11_1 ),
    inference(resolution,[],[f184,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f184,plain,
    ( r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(sK1,sK2))
    | ~ spl11_1 ),
    inference(resolution,[],[f133,f72])).

fof(f234,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = X0
        | ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) )
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f233,f201])).

fof(f201,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f196,f66])).

fof(f196,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f184,f73])).

fof(f233,plain,
    ( ! [X0] :
        ( sK5 != k4_tarski(k1_mcart_1(sK5),X0)
        | sK4 = X0
        | ~ m1_subset_1(X0,sK3)
        | ~ m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2)
        | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) )
    | ~ spl11_1 ),
    inference(superposition,[],[f93,f228])).

fof(f228,plain,
    ( k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5)))
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f214,f213])).

fof(f213,plain,
    ( sK9(k1_mcart_1(sK5)) = k1_mcart_1(k1_mcart_1(sK5))
    | ~ spl11_1 ),
    inference(superposition,[],[f63,f195])).

fof(f195,plain,
    ( k1_mcart_1(sK5) = k4_tarski(sK9(k1_mcart_1(sK5)),sK10(k1_mcart_1(sK5)))
    | ~ spl11_1 ),
    inference(resolution,[],[f184,f85])).

fof(f214,plain,
    ( k1_mcart_1(sK5) = k4_tarski(sK9(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5)))
    | ~ spl11_1 ),
    inference(backward_demodulation,[],[f195,f212])).

fof(f212,plain,
    ( sK10(k1_mcart_1(sK5)) = k2_mcart_1(k1_mcart_1(sK5))
    | ~ spl11_1 ),
    inference(superposition,[],[f64,f195])).

fof(f93,plain,(
    ! [X6,X7,X5] :
      ( sK5 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK4 = X7
      | ~ m1_subset_1(X7,sK3)
      | ~ m1_subset_1(X6,sK2)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f51,plain,(
    ! [X6,X7,X5] :
      ( sK4 = X7
      | k3_mcart_1(X5,X6,X7) != sK5
      | ~ m1_subset_1(X7,sK3)
      | ~ m1_subset_1(X6,sK2)
      | ~ m1_subset_1(X5,sK1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f260,plain,(
    k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) ),
    inference(subsumption_resolution,[],[f259,f52])).

fof(f52,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f31])).

fof(f259,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f258,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f31])).

fof(f258,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f252,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

fof(f252,plain,
    ( k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f97,f94])).

fof(f94,plain,(
    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f50,plain,(
    m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f84,f71])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f180,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f178,f53])).

fof(f178,plain,
    ( k1_xboole_0 = sK2
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f177,f52])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl11_2 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | ~ spl11_2 ),
    inference(superposition,[],[f67,f171])).

fof(f171,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f170,f54])).

fof(f170,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_zfmisc_1(sK1,sK2)
    | k1_xboole_0 = sK3
    | ~ spl11_2 ),
    inference(superposition,[],[f67,f139])).

fof(f139,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)
    | ~ spl11_2 ),
    inference(resolution,[],[f137,f122])).

fof(f122,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f58,f56])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f137,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl11_2
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f138,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f127,f135,f131])).

fof(f127,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))
    | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) ),
    inference(resolution,[],[f65,f94])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (11127)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (11143)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (11127)Refutation not found, incomplete strategy% (11127)------------------------------
% 0.20/0.52  % (11127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11135)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (11135)Refutation not found, incomplete strategy% (11135)------------------------------
% 0.20/0.52  % (11135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (11127)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11127)Memory used [KB]: 10874
% 0.20/0.52  % (11127)Time elapsed: 0.098 s
% 0.20/0.52  % (11127)------------------------------
% 0.20/0.52  % (11127)------------------------------
% 0.20/0.52  % (11135)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (11135)Memory used [KB]: 1663
% 0.20/0.52  % (11135)Time elapsed: 0.107 s
% 0.20/0.52  % (11135)------------------------------
% 0.20/0.52  % (11135)------------------------------
% 0.20/0.53  % (11143)Refutation not found, incomplete strategy% (11143)------------------------------
% 0.20/0.53  % (11143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (11143)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (11143)Memory used [KB]: 6268
% 0.20/0.53  % (11143)Time elapsed: 0.103 s
% 0.20/0.53  % (11143)------------------------------
% 0.20/0.53  % (11143)------------------------------
% 0.20/0.54  % (11122)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.34/0.54  % (11131)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (11121)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % (11123)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (11118)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.54  % (11126)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (11118)Refutation not found, incomplete strategy% (11118)------------------------------
% 1.34/0.54  % (11118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (11118)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (11118)Memory used [KB]: 1663
% 1.34/0.54  % (11118)Time elapsed: 0.124 s
% 1.34/0.54  % (11118)------------------------------
% 1.34/0.54  % (11118)------------------------------
% 1.34/0.54  % (11131)Refutation not found, incomplete strategy% (11131)------------------------------
% 1.34/0.54  % (11131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (11131)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (11131)Memory used [KB]: 1791
% 1.34/0.54  % (11131)Time elapsed: 0.050 s
% 1.34/0.54  % (11131)------------------------------
% 1.34/0.54  % (11131)------------------------------
% 1.34/0.54  % (11124)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.55  % (11119)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.55  % (11137)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.55  % (11117)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.55  % (11125)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (11120)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.55  % (11123)Refutation found. Thanks to Tanya!
% 1.34/0.55  % SZS status Theorem for theBenchmark
% 1.34/0.55  % SZS output start Proof for theBenchmark
% 1.34/0.55  fof(f264,plain,(
% 1.34/0.55    $false),
% 1.34/0.55    inference(avatar_sat_refutation,[],[f138,f180,f263])).
% 1.34/0.55  fof(f263,plain,(
% 1.34/0.55    ~spl11_1),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f262])).
% 1.34/0.55  fof(f262,plain,(
% 1.34/0.55    $false | ~spl11_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f261,f55])).
% 1.34/0.55  fof(f55,plain,(
% 1.34/0.55    sK4 != k7_mcart_1(sK1,sK2,sK3,sK5)),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f31,plain,(
% 1.34/0.55    sK4 != k7_mcart_1(sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5] : (! [X6] : (! [X7] : (sK4 = X7 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3)) | ~m1_subset_1(X6,sK2)) | ~m1_subset_1(X5,sK1)) & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f20,f30])).
% 1.34/0.55  fof(f30,plain,(
% 1.34/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK4 != k7_mcart_1(sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X5] : (! [X6] : (! [X7] : (sK4 = X7 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3)) | ~m1_subset_1(X6,sK2)) | ~m1_subset_1(X5,sK1)) & m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3)))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f20,plain,(
% 1.34/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.55    inference(flattening,[],[f19])).
% 1.34/0.55  fof(f19,plain,(
% 1.34/0.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.55    inference(ennf_transformation,[],[f18])).
% 1.34/0.55  fof(f18,negated_conjecture,(
% 1.34/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.34/0.55    inference(negated_conjecture,[],[f17])).
% 1.34/0.55  fof(f17,conjecture,(
% 1.34/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 1.34/0.55  fof(f261,plain,(
% 1.34/0.55    sK4 = k7_mcart_1(sK1,sK2,sK3,sK5) | ~spl11_1),
% 1.34/0.55    inference(forward_demodulation,[],[f260,f238])).
% 1.34/0.55  fof(f238,plain,(
% 1.34/0.55    sK4 = k2_mcart_1(sK5) | ~spl11_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f237,f187])).
% 1.34/0.55  fof(f187,plain,(
% 1.34/0.55    m1_subset_1(k2_mcart_1(sK5),sK3) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f183,f66])).
% 1.34/0.55  fof(f66,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f24])).
% 1.34/0.55  fof(f24,plain,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f7])).
% 1.34/0.55  fof(f7,axiom,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.34/0.55  fof(f183,plain,(
% 1.34/0.55    r2_hidden(k2_mcart_1(sK5),sK3) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f133,f73])).
% 1.34/0.55  fof(f73,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f25])).
% 1.34/0.55  fof(f25,plain,(
% 1.34/0.55    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.34/0.55    inference(ennf_transformation,[],[f12])).
% 1.34/0.55  fof(f12,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 1.34/0.55  fof(f133,plain,(
% 1.34/0.55    r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl11_1),
% 1.34/0.55    inference(avatar_component_clause,[],[f131])).
% 1.34/0.55  fof(f131,plain,(
% 1.34/0.55    spl11_1 <=> r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.34/0.55  fof(f237,plain,(
% 1.34/0.55    sK4 = k2_mcart_1(sK5) | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~spl11_1),
% 1.34/0.55    inference(trivial_inequality_removal,[],[f236])).
% 1.34/0.55  fof(f236,plain,(
% 1.34/0.55    sK5 != sK5 | sK4 = k2_mcart_1(sK5) | ~m1_subset_1(k2_mcart_1(sK5),sK3) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f235,f211])).
% 1.34/0.55  fof(f211,plain,(
% 1.34/0.55    sK5 = k4_tarski(k1_mcart_1(sK5),k2_mcart_1(sK5)) | ~spl11_1),
% 1.34/0.55    inference(forward_demodulation,[],[f210,f209])).
% 1.34/0.55  fof(f209,plain,(
% 1.34/0.55    k1_mcart_1(sK5) = sK9(sK5) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f63,f189])).
% 1.34/0.55  fof(f189,plain,(
% 1.34/0.55    sK5 = k4_tarski(sK9(sK5),sK10(sK5)) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f85,f133])).
% 1.34/0.55  fof(f85,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK9(X0),sK10(X0)) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f47])).
% 1.34/0.55  fof(f47,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (k4_tarski(sK9(X0),sK10(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f27,f46])).
% 1.34/0.55  fof(f46,plain,(
% 1.34/0.55    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK9(X0),sK10(X0)) = X0)),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f27,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.34/0.55    inference(ennf_transformation,[],[f4])).
% 1.34/0.55  fof(f4,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 1.34/0.55  % (11139)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.55  fof(f63,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f16,axiom,(
% 1.34/0.55    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 1.34/0.55  fof(f210,plain,(
% 1.34/0.55    sK5 = k4_tarski(sK9(sK5),k2_mcart_1(sK5)) | ~spl11_1),
% 1.34/0.55    inference(backward_demodulation,[],[f189,f208])).
% 1.34/0.55  fof(f208,plain,(
% 1.34/0.55    k2_mcart_1(sK5) = sK10(sK5) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f64,f189])).
% 1.34/0.55  fof(f64,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f16])).
% 1.34/0.55  fof(f235,plain,(
% 1.34/0.55    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = X0 | ~m1_subset_1(X0,sK3)) ) | ~spl11_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f234,f203])).
% 1.34/0.55  fof(f203,plain,(
% 1.34/0.55    m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f197,f66])).
% 1.34/0.55  fof(f197,plain,(
% 1.34/0.55    r2_hidden(k1_mcart_1(k1_mcart_1(sK5)),sK1) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f184,f72])).
% 1.34/0.55  fof(f72,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f25])).
% 1.34/0.55  fof(f184,plain,(
% 1.34/0.55    r2_hidden(k1_mcart_1(sK5),k2_zfmisc_1(sK1,sK2)) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f133,f72])).
% 1.34/0.55  fof(f234,plain,(
% 1.34/0.55    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = X0 | ~m1_subset_1(X0,sK3) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)) ) | ~spl11_1),
% 1.34/0.55    inference(subsumption_resolution,[],[f233,f201])).
% 1.34/0.55  fof(f201,plain,(
% 1.34/0.55    m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f196,f66])).
% 1.34/0.55  fof(f196,plain,(
% 1.34/0.55    r2_hidden(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f184,f73])).
% 1.34/0.55  fof(f233,plain,(
% 1.34/0.55    ( ! [X0] : (sK5 != k4_tarski(k1_mcart_1(sK5),X0) | sK4 = X0 | ~m1_subset_1(X0,sK3) | ~m1_subset_1(k2_mcart_1(k1_mcart_1(sK5)),sK2) | ~m1_subset_1(k1_mcart_1(k1_mcart_1(sK5)),sK1)) ) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f93,f228])).
% 1.34/0.55  fof(f228,plain,(
% 1.34/0.55    k1_mcart_1(sK5) = k4_tarski(k1_mcart_1(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) | ~spl11_1),
% 1.34/0.55    inference(forward_demodulation,[],[f214,f213])).
% 1.34/0.55  fof(f213,plain,(
% 1.34/0.55    sK9(k1_mcart_1(sK5)) = k1_mcart_1(k1_mcart_1(sK5)) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f63,f195])).
% 1.34/0.55  fof(f195,plain,(
% 1.34/0.55    k1_mcart_1(sK5) = k4_tarski(sK9(k1_mcart_1(sK5)),sK10(k1_mcart_1(sK5))) | ~spl11_1),
% 1.34/0.55    inference(resolution,[],[f184,f85])).
% 1.34/0.55  fof(f214,plain,(
% 1.34/0.55    k1_mcart_1(sK5) = k4_tarski(sK9(k1_mcart_1(sK5)),k2_mcart_1(k1_mcart_1(sK5))) | ~spl11_1),
% 1.34/0.55    inference(backward_demodulation,[],[f195,f212])).
% 1.34/0.55  fof(f212,plain,(
% 1.34/0.55    sK10(k1_mcart_1(sK5)) = k2_mcart_1(k1_mcart_1(sK5)) | ~spl11_1),
% 1.34/0.55    inference(superposition,[],[f64,f195])).
% 1.34/0.55  fof(f93,plain,(
% 1.34/0.55    ( ! [X6,X7,X5] : (sK5 != k4_tarski(k4_tarski(X5,X6),X7) | sK4 = X7 | ~m1_subset_1(X7,sK3) | ~m1_subset_1(X6,sK2) | ~m1_subset_1(X5,sK1)) )),
% 1.34/0.55    inference(definition_unfolding,[],[f51,f70])).
% 1.34/0.55  fof(f70,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f9])).
% 1.34/0.55  fof(f9,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.34/0.55  fof(f51,plain,(
% 1.34/0.55    ( ! [X6,X7,X5] : (sK4 = X7 | k3_mcart_1(X5,X6,X7) != sK5 | ~m1_subset_1(X7,sK3) | ~m1_subset_1(X6,sK2) | ~m1_subset_1(X5,sK1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f260,plain,(
% 1.34/0.55    k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5)),
% 1.34/0.55    inference(subsumption_resolution,[],[f259,f52])).
% 1.34/0.55  fof(f52,plain,(
% 1.34/0.55    k1_xboole_0 != sK1),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f259,plain,(
% 1.34/0.55    k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK1),
% 1.34/0.55    inference(subsumption_resolution,[],[f258,f53])).
% 1.34/0.55  fof(f53,plain,(
% 1.34/0.55    k1_xboole_0 != sK2),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f258,plain,(
% 1.34/0.55    k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.34/0.55    inference(subsumption_resolution,[],[f252,f54])).
% 1.34/0.55  fof(f54,plain,(
% 1.34/0.55    k1_xboole_0 != sK3),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f252,plain,(
% 1.34/0.55    k7_mcart_1(sK1,sK2,sK3,sK5) = k2_mcart_1(sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.34/0.55    inference(resolution,[],[f97,f94])).
% 1.34/0.55  fof(f94,plain,(
% 1.34/0.55    m1_subset_1(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.34/0.55    inference(definition_unfolding,[],[f50,f71])).
% 1.34/0.55  fof(f71,plain,(
% 1.34/0.55    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f10])).
% 1.34/0.55  fof(f10,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.34/0.55  fof(f50,plain,(
% 1.34/0.55    m1_subset_1(sK5,k3_zfmisc_1(sK1,sK2,sK3))),
% 1.34/0.55    inference(cnf_transformation,[],[f31])).
% 1.34/0.55  fof(f97,plain,(
% 1.34/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.34/0.55    inference(definition_unfolding,[],[f84,f71])).
% 1.34/0.55  fof(f84,plain,(
% 1.34/0.55    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f26])).
% 1.34/0.55  fof(f26,plain,(
% 1.34/0.55    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.34/0.55    inference(ennf_transformation,[],[f14])).
% 1.34/0.55  fof(f14,axiom,(
% 1.34/0.55    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 1.34/0.55  fof(f180,plain,(
% 1.34/0.55    ~spl11_2),
% 1.34/0.55    inference(avatar_contradiction_clause,[],[f179])).
% 1.34/0.55  fof(f179,plain,(
% 1.34/0.55    $false | ~spl11_2),
% 1.34/0.55    inference(subsumption_resolution,[],[f178,f53])).
% 1.34/0.55  fof(f178,plain,(
% 1.34/0.55    k1_xboole_0 = sK2 | ~spl11_2),
% 1.34/0.55    inference(subsumption_resolution,[],[f177,f52])).
% 1.34/0.55  fof(f177,plain,(
% 1.34/0.55    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl11_2),
% 1.34/0.55    inference(trivial_inequality_removal,[],[f173])).
% 1.34/0.55  fof(f173,plain,(
% 1.34/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | ~spl11_2),
% 1.34/0.55    inference(superposition,[],[f67,f171])).
% 1.34/0.55  fof(f171,plain,(
% 1.34/0.55    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | ~spl11_2),
% 1.34/0.55    inference(subsumption_resolution,[],[f170,f54])).
% 1.34/0.55  fof(f170,plain,(
% 1.34/0.55    k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | k1_xboole_0 = sK3 | ~spl11_2),
% 1.34/0.55    inference(trivial_inequality_removal,[],[f169])).
% 1.34/0.55  fof(f169,plain,(
% 1.34/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_zfmisc_1(sK1,sK2) | k1_xboole_0 = sK3 | ~spl11_2),
% 1.34/0.55    inference(superposition,[],[f67,f139])).
% 1.34/0.55  fof(f139,plain,(
% 1.34/0.55    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3) | ~spl11_2),
% 1.34/0.55    inference(resolution,[],[f137,f122])).
% 1.34/0.55  fof(f122,plain,(
% 1.34/0.55    ( ! [X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X1) )),
% 1.34/0.55    inference(resolution,[],[f58,f56])).
% 1.34/0.55  fof(f56,plain,(
% 1.34/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f35])).
% 1.34/0.55  fof(f35,plain,(
% 1.34/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f33,f34])).
% 1.34/0.55  fof(f34,plain,(
% 1.34/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f33,plain,(
% 1.34/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.55    inference(rectify,[],[f32])).
% 1.34/0.55  fof(f32,plain,(
% 1.34/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.34/0.55    inference(nnf_transformation,[],[f1])).
% 1.34/0.55  fof(f1,axiom,(
% 1.34/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.34/0.55  fof(f58,plain,(
% 1.34/0.55    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.55    inference(cnf_transformation,[],[f37])).
% 1.34/0.55  fof(f37,plain,(
% 1.34/0.55    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 1.34/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f21,f36])).
% 1.34/0.55  fof(f36,plain,(
% 1.34/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 1.34/0.55    introduced(choice_axiom,[])).
% 1.34/0.55  fof(f21,plain,(
% 1.34/0.55    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.34/0.55    inference(ennf_transformation,[],[f13])).
% 1.34/0.55  fof(f13,axiom,(
% 1.34/0.55    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 1.34/0.55  fof(f137,plain,(
% 1.34/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | ~spl11_2),
% 1.34/0.55    inference(avatar_component_clause,[],[f135])).
% 1.34/0.55  fof(f135,plain,(
% 1.34/0.55    spl11_2 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.34/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.34/0.55  fof(f67,plain,(
% 1.34/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 1.34/0.55    inference(cnf_transformation,[],[f39])).
% 1.34/0.55  fof(f39,plain,(
% 1.34/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.34/0.55    inference(flattening,[],[f38])).
% 1.34/0.55  fof(f38,plain,(
% 1.34/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.34/0.55    inference(nnf_transformation,[],[f5])).
% 1.34/0.55  fof(f5,axiom,(
% 1.34/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.34/0.55  fof(f138,plain,(
% 1.34/0.55    spl11_1 | spl11_2),
% 1.34/0.55    inference(avatar_split_clause,[],[f127,f135,f131])).
% 1.34/0.55  fof(f127,plain,(
% 1.34/0.55    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3)) | r2_hidden(sK5,k2_zfmisc_1(k2_zfmisc_1(sK1,sK2),sK3))),
% 1.34/0.55    inference(resolution,[],[f65,f94])).
% 1.34/0.55  fof(f65,plain,(
% 1.34/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.34/0.55    inference(cnf_transformation,[],[f23])).
% 1.34/0.55  fof(f23,plain,(
% 1.34/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.34/0.55    inference(flattening,[],[f22])).
% 1.34/0.55  fof(f22,plain,(
% 1.34/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.34/0.55    inference(ennf_transformation,[],[f8])).
% 1.34/0.55  fof(f8,axiom,(
% 1.34/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.34/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.34/0.55  % SZS output end Proof for theBenchmark
% 1.34/0.55  % (11123)------------------------------
% 1.34/0.55  % (11123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (11123)Termination reason: Refutation
% 1.34/0.55  
% 1.34/0.55  % (11134)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.55  % (11123)Memory used [KB]: 10874
% 1.46/0.55  % (11123)Time elapsed: 0.059 s
% 1.46/0.55  % (11123)------------------------------
% 1.46/0.55  % (11123)------------------------------
% 1.46/0.56  % (11141)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.46/0.56  % (11114)Success in time 0.189 s
%------------------------------------------------------------------------------
