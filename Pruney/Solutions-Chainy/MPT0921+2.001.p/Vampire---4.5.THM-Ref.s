%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 (1026 expanded)
%              Number of leaves         :   10 ( 305 expanded)
%              Depth                    :   56
%              Number of atoms          :  508 (10802 expanded)
%              Number of equality atoms :  344 (6240 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f216,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f24])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK4 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != sK5
                    | ~ m1_subset_1(X9,sK3) )
                | ~ m1_subset_1(X8,sK2) )
            | ~ m1_subset_1(X7,sK1) )
        | ~ m1_subset_1(X6,sK0) )
    & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X8
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != sK5
                      | ~ m1_subset_1(X9,sK3) )
                  | ~ m1_subset_1(X8,sK2) )
              | ~ m1_subset_1(X7,sK1) )
          | ~ m1_subset_1(X6,sK0) )
      & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

% (21826)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k10_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
       => ( ! [X6] :
              ( m1_subset_1(X6,X0)
             => ! [X7] :
                  ( m1_subset_1(X7,X1)
                 => ! [X8] :
                      ( m1_subset_1(X8,X2)
                     => ! [X9] :
                          ( m1_subset_1(X9,X3)
                         => ( k4_mcart_1(X6,X7,X8,X9) = X5
                           => X4 = X8 ) ) ) ) )
         => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))
     => ( ! [X6] :
            ( m1_subset_1(X6,X0)
           => ! [X7] :
                ( m1_subset_1(X7,X1)
               => ! [X8] :
                    ( m1_subset_1(X8,X2)
                   => ! [X9] :
                        ( m1_subset_1(X9,X3)
                       => ( k4_mcart_1(X6,X7,X8,X9) = X5
                         => X4 = X8 ) ) ) ) )
       => ( k10_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

fof(f215,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f214,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f214,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f213,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f213,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f212,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f12])).

fof(f212,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f211,f28])).

fof(f28,plain,(
    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f12])).

fof(f211,plain,
    ( sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f210,f117])).

fof(f117,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f116,f24])).

fof(f116,plain,
    ( m1_subset_1(sK4,sK2)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f115,f25])).

fof(f115,plain,
    ( m1_subset_1(sK4,sK2)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f114,f26])).

fof(f114,plain,
    ( m1_subset_1(sK4,sK2)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f113,f27])).

fof(f113,plain,
    ( m1_subset_1(sK4,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f112,f22])).

fof(f22,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f112,plain,
    ( m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f110])).

fof(f110,plain,(
    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f109,f24])).

fof(f109,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f108,f25])).

fof(f108,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f107,f26])).

fof(f107,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f106,f27])).

fof(f106,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f105,f22])).

fof(f105,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f104,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4
            & m1_subset_1(sK13(X0,X1,X2,X3,X4),X3)
            & m1_subset_1(sK12(X0,X1,X2,X3,X4),X2)
            & m1_subset_1(sK11(X0,X1,X2,X3,X4),X1)
            & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f9,f20,f19,f18,f17])).

fof(f17,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( k4_mcart_1(X5,X6,X7,X8) = X4
                      & m1_subset_1(X8,X3) )
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                    & m1_subset_1(X8,X3) )
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( ? [X8] :
                ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),X7,X8) = X4
                & m1_subset_1(X8,X3) )
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK11(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ? [X8] :
              ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),X7,X8) = X4
              & m1_subset_1(X8,X3) )
          & m1_subset_1(X7,X2) )
     => ( ? [X8] :
            ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X8) = X4
            & m1_subset_1(X8,X3) )
        & m1_subset_1(sK12(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X8) = X4
          & m1_subset_1(X8,X3) )
     => ( k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK13(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

% (21818)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ? [X7] :
                      ( ? [X8] :
                          ( k4_mcart_1(X5,X6,X7,X8) = X4
                          & m1_subset_1(X8,X3) )
                      & m1_subset_1(X7,X2) )
                  & m1_subset_1(X6,X1) )
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ? [X4] :
            ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ! [X6] :
                    ( m1_subset_1(X6,X1)
                   => ! [X7] :
                        ( m1_subset_1(X7,X2)
                       => ! [X8] :
                            ( m1_subset_1(X8,X3)
                           => k4_mcart_1(X5,X6,X7,X8) != X4 ) ) ) )
            & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

fof(f104,plain,
    ( ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | sK4 = sK12(sK0,sK1,sK2,sK3,sK5) ),
    inference(subsumption_resolution,[],[f103,f24])).

fof(f103,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f102,f25])).

fof(f102,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f101,f26])).

fof(f101,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f100,f27])).

fof(f100,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f99,f22])).

fof(f99,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK11(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,
    ( ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f96,f25])).

fof(f96,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f95,f26])).

fof(f95,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f94,f27])).

fof(f94,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f93,f22])).

fof(f93,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f92,f34])).

fof(f92,plain,
    ( ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(subsumption_resolution,[],[f91,f24])).

fof(f91,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f90,f25])).

fof(f90,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f89,f26])).

fof(f89,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f88,f27])).

fof(f88,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f87,plain,
    ( sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f82,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK13(X0,X1,X2,X3,X4),X3)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,
    ( ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)
    | sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,
    ( sK5 != sK5
    | sK4 = sK12(sK0,sK1,sK2,sK3,sK5)
    | ~ m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2)
    | ~ m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1)
    | ~ m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) ),
    inference(superposition,[],[f23,f72])).

fof(f72,plain,(
    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) ),
    inference(subsumption_resolution,[],[f71,f24])).

fof(f71,plain,
    ( sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f70,f25])).

fof(f70,plain,
    ( sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f27])).

fof(f64,plain,
    ( sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f36,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X8
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X6,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK12(X0,X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f210,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f141,f22])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(sK4,X2)
      | sK4 = k10_mcart_1(X0,X1,X2,X3,sK5)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(trivial_inequality_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( sK4 != sK4
      | sK4 = k10_mcart_1(X0,X1,X2,X3,sK5)
      | ~ m1_subset_1(sK4,X2)
      | ~ m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f31,f138])).

fof(f138,plain,(
    sK4 = sK8(sK5,sK4) ),
    inference(forward_demodulation,[],[f134,f110])).

fof(f134,plain,(
    sK12(sK0,sK1,sK2,sK3,sK5) = sK8(sK5,sK4) ),
    inference(trivial_inequality_removal,[],[f131])).

fof(f131,plain,
    ( sK5 != sK5
    | sK12(sK0,sK1,sK2,sK3,sK5) = sK8(sK5,sK4) ),
    inference(superposition,[],[f78,f119])).

fof(f119,plain,(
    sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4)) ),
    inference(subsumption_resolution,[],[f118,f28])).

fof(f118,plain,
    ( sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4))
    | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(resolution,[],[f117,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 ) ),
    inference(subsumption_resolution,[],[f54,f24])).

fof(f54,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | ~ m1_subset_1(X0,sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f53,f25])).

fof(f53,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | ~ m1_subset_1(X0,sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f52,f26])).

fof(f52,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | ~ m1_subset_1(X0,sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(subsumption_resolution,[],[f47,f27])).

fof(f47,plain,(
    ! [X0] :
      ( sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0))
      | ~ m1_subset_1(X0,sK2)
      | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4
      | ~ m1_subset_1(X5,X2)
      | k10_mcart_1(X0,X1,X2,X3,X4) = X5
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK8(X4,X5) != X5
                    & k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f15])).

fof(f15,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X8
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK8(X4,X5) != X5
        & k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X12
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X8
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X8
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k10_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X8
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X2) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X2)
                 => ( k10_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X8 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).

fof(f78,plain,(
    ! [X19,X17,X18,X16] :
      ( sK5 != k4_mcart_1(X16,X17,X18,X19)
      | sK12(sK0,sK1,sK2,sK3,sK5) = X18 ) ),
    inference(superposition,[],[f39,f72])).

fof(f39,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7)
      | X2 = X6 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 )
      | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7)
     => ( X3 = X7
        & X2 = X6
        & X1 = X5
        & X0 = X4 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK8(X4,X5) != X5
      | k10_mcart_1(X0,X1,X2,X3,X4) = X5
      | ~ m1_subset_1(X5,X2)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:51:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (21827)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (21835)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.49  % (21835)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    k1_xboole_0 != sK0),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5) & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK4 = X8 | k4_mcart_1(X6,X7,X8,X9) != sK5 | ~m1_subset_1(X9,sK3)) | ~m1_subset_1(X8,sK2)) | ~m1_subset_1(X7,sK1)) | ~m1_subset_1(X6,sK0)) & m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (21826)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5] : (k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2,X3,X4,X5] : (((k10_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X8 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X8))))) => (k10_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f213,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    k1_xboole_0 != sK2),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    k1_xboole_0 != sK3),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f211,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    sK4 != k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f210,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f24])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f115,f25])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f114,f26])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f113,f27])).
% 0.21/0.49  fof(f113,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f112,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    m1_subset_1(sK4,sK2) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(superposition,[],[f34,f110])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f24])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f108,f25])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f107,f26])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f106,f27])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f105,f22])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f104,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK10(X0,X1,X2,X3,X4),X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (((((k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK13(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK12(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK11(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12,sK13])],[f9,f20,f19,f18,f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK10(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(sK11(X0,X1,X2,X3,X4),X1)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X4,X3,X2,X1,X0] : (? [X7] : (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) => (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(sK12(X0,X1,X2,X3,X4),X2)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X4,X3,X2,X1,X0] : (? [X8] : (k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X8) = X4 & m1_subset_1(X8,X3)) => (k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK13(X0,X1,X2,X3,X4),X3)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  % (21818)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | sK4 = sK12(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f103,f24])).
% 0.21/0.49  fof(f103,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f102,f25])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f101,f26])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f100,f27])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f99,f22])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f98,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK11(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f97,f24])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f96,f25])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f26])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f94,f27])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f93,f22])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f92,f34])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f24])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f25])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f26])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f27])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f22])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f82,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK13(X0,X1,X2,X3,X4),X3) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) | sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    sK5 != sK5 | sK4 = sK12(sK0,sK1,sK2,sK3,sK5) | ~m1_subset_1(sK13(sK0,sK1,sK2,sK3,sK5),sK3) | ~m1_subset_1(sK12(sK0,sK1,sK2,sK3,sK5),sK2) | ~m1_subset_1(sK11(sK0,sK1,sK2,sK3,sK5),sK1) | ~m1_subset_1(sK10(sK0,sK1,sK2,sK3,sK5),sK0)),
% 0.21/0.49    inference(superposition,[],[f23,f72])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5))),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f24])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f25])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f26])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f27])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK10(sK0,sK1,sK2,sK3,sK5),sK11(sK0,sK1,sK2,sK3,sK5),sK12(sK0,sK1,sK2,sK3,sK5),sK13(sK0,sK1,sK2,sK3,sK5)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f36,f22])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK10(X0,X1,X2,X3,X4),sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X8 | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X6,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK12(X0,X1,X2,X3,X4),X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    ~m1_subset_1(sK4,sK2) | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.49    inference(resolution,[],[f141,f22])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(sK4,X2) | sK4 = k10_mcart_1(X0,X1,X2,X3,sK5) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (sK4 != sK4 | sK4 = k10_mcart_1(X0,X1,X2,X3,sK5) | ~m1_subset_1(sK4,X2) | ~m1_subset_1(sK5,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(superposition,[],[f31,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    sK4 = sK8(sK5,sK4)),
% 0.21/0.49    inference(forward_demodulation,[],[f134,f110])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    sK12(sK0,sK1,sK2,sK3,sK5) = sK8(sK5,sK4)),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    sK5 != sK5 | sK12(sK0,sK1,sK2,sK3,sK5) = sK8(sK5,sK4)),
% 0.21/0.49    inference(superposition,[],[f78,f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4))),
% 0.21/0.49    inference(subsumption_resolution,[],[f118,f28])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    sK5 = k4_mcart_1(sK6(sK5,sK4),sK7(sK5,sK4),sK8(sK5,sK4),sK9(sK5,sK4)) | sK4 = k10_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.21/0.49    inference(resolution,[],[f117,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,sK2) | sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f24])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | ~m1_subset_1(X0,sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f25])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | ~m1_subset_1(X0,sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f26])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | ~m1_subset_1(X0,sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f47,f27])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (sK5 = k4_mcart_1(sK6(sK5,X0),sK7(sK5,X0),sK8(sK5,X0),sK9(sK5,X0)) | ~m1_subset_1(X0,sK2) | k10_mcart_1(sK0,sK1,sK2,sK3,sK5) = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 0.21/0.49    inference(resolution,[],[f30,f22])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4 | ~m1_subset_1(X5,X2) | k10_mcart_1(X0,X1,X2,X3,X4) = X5 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK8(X4,X5) != X5 & k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f14,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK8(X4,X5) != X5 & k4_mcart_1(sK6(X4,X5),sK7(X4,X5),sK8(X4,X5),sK9(X4,X5)) = X4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X12 | k4_mcart_1(X10,X11,X12,X13) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(rectify,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X8 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4) | k10_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X8 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X2)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X2) => (k10_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X8)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_mcart_1)).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X19,X17,X18,X16] : (sK5 != k4_mcart_1(X16,X17,X18,X19) | sK12(sK0,sK1,sK2,sK3,sK5) = X18) )),
% 0.21/0.49    inference(superposition,[],[f39,f72])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7) | X2 = X6) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4) | k4_mcart_1(X0,X1,X2,X3) != k4_mcart_1(X4,X5,X6,X7))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k4_mcart_1(X0,X1,X2,X3) = k4_mcart_1(X4,X5,X6,X7) => (X3 = X7 & X2 = X6 & X1 = X5 & X0 = X4))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_mcart_1)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (sK8(X4,X5) != X5 | k10_mcart_1(X0,X1,X2,X3,X4) = X5 | ~m1_subset_1(X5,X2) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21835)------------------------------
% 0.21/0.49  % (21835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21835)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21835)Memory used [KB]: 6396
% 0.21/0.49  % (21835)Time elapsed: 0.087 s
% 0.21/0.49  % (21835)------------------------------
% 0.21/0.49  % (21835)------------------------------
% 0.21/0.49  % (21812)Success in time 0.139 s
%------------------------------------------------------------------------------
