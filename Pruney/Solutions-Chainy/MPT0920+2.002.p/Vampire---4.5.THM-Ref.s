%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 287 expanded)
%              Number of leaves         :   11 (  85 expanded)
%              Depth                    :   34
%              Number of atoms          :  489 (2491 expanded)
%              Number of equality atoms :  335 (1435 expanded)
%              Maximal formula depth    :   24 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f33,f169])).

fof(f169,plain,(
    k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f34,f145])).

fof(f145,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f35,f124])).

fof(f124,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f36,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3 ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( sK5 != sK5
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f37,f92])).

fof(f92,plain,
    ( sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,
    ( sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f89,f71])).

fof(f71,plain,
    ( m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f70])).

fof(f70,plain,
    ( m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f53,f66])).

fof(f66,plain,
    ( k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f65,f31])).

fof(f31,plain,(
    m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & ! [X6] :
        ( ! [X7] :
            ( ! [X8] :
                ( ! [X9] :
                    ( sK5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != sK6
                    | ~ m1_subset_1(X9,sK4) )
                | ~ m1_subset_1(X8,sK3) )
            | ~ m1_subset_1(X7,sK2) )
        | ~ m1_subset_1(X6,sK1) )
    & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( ! [X9] :
                        ( X4 = X7
                        | k4_mcart_1(X6,X7,X8,X9) != X5
                        | ~ m1_subset_1(X9,X3) )
                    | ~ m1_subset_1(X8,X2) )
                | ~ m1_subset_1(X7,X1) )
            | ~ m1_subset_1(X6,X0) )
        & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) )
   => ( sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( sK5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != sK6
                      | ~ m1_subset_1(X9,sK4) )
                  | ~ m1_subset_1(X8,sK3) )
              | ~ m1_subset_1(X7,sK2) )
          | ~ m1_subset_1(X6,sK1) )
      & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k9_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                           => X4 = X7 ) ) ) ) )
         => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                         => X4 = X7 ) ) ) ) )
       => ( k9_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

fof(f65,plain,
    ( ~ m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4))
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) ),
    inference(resolution,[],[f64,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

fof(f64,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f61,f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK6,k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,sK6),X1)
      | sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) = k9_mcart_1(X0,X1,X2,X3,sK6)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK4 ) ),
    inference(superposition,[],[f49,f56])).

fof(f56,plain,
    ( sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f51,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0
        & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)
        & m1_subset_1(sK12(X0,X1,X2,X3,X4),X3)
        & m1_subset_1(sK11(X0,X1,X2,X3,X4),X4) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f24,f27,f26,f25])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( k4_mcart_1(X1,X5,X6,X7) = X0
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X3) )
          & m1_subset_1(X5,X4) )
     => ( ? [X6] :
            ( ? [X7] :
                ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),X6,X7) = X0
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X3) )
        & m1_subset_1(sK11(X0,X1,X2,X3,X4),X4) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),X6,X7) = X0
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X3) )
     => ( ? [X7] :
            ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7) = X0
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK12(X0,X1,X2,X3,X4),X3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7) = X0
          & m1_subset_1(X7,X2) )
     => ( k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0
        & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

% (19628)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (19621)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (19619)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (19639)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (19636)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (19631)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (19630)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (19626)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (19642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( k4_mcart_1(X1,X5,X6,X7) = X0
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X3) )
          & m1_subset_1(X5,X4) )
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X4,X5,X3,X2,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
      | ~ sP0(X4,X5,X3,X2,X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X4,X5,X3,X2,X1] :
      ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( k4_mcart_1(X5,X6,X7,X8) = X4
                  & m1_subset_1(X8,X3) )
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
      | ~ sP0(X4,X5,X3,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f51,plain,
    ( sP0(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1)
            & m1_subset_1(sK14(X0,X1,X2,X3,X4),X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f16,f29])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( sP0(X4,X5,X3,X2,X1)
          & m1_subset_1(X5,X0) )
     => ( sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1)
        & m1_subset_1(sK14(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ? [X5] :
              ( sP0(X4,X5,X3,X2,X1)
              & m1_subset_1(X5,X0) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f14,f15])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f49,plain,(
    ! [X2,X0,X12,X10,X3,X1,X13,X11] :
      ( ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | ~ m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1)
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] :
      ( X5 = X11
      | k4_mcart_1(X10,X11,X12,X13) != X4
      | k9_mcart_1(X0,X1,X2,X3,X4) != X5
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ( sK8(X4,X5) != X5
                    & k4_mcart_1(sK7(X4,X5),sK8(X4,X5),sK9(X4,X5),sK10(X4,X5)) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f20,f21])).

fof(f21,plain,(
    ! [X5,X4] :
      ( ? [X6,X7,X8,X9] :
          ( X5 != X7
          & k4_mcart_1(X6,X7,X8,X9) = X4 )
     => ( sK8(X4,X5) != X5
        & k4_mcart_1(sK7(X4,X5),sK8(X4,X5),sK9(X4,X5),sK10(X4,X5)) = X4 ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X10,X11,X12,X13] :
                      ( X5 = X11
                      | k4_mcart_1(X10,X11,X12,X13) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  | ? [X6,X7,X8,X9] :
                      ( X5 != X7
                      & k4_mcart_1(X6,X7,X8,X9) = X4 ) )
                & ( ! [X6,X7,X8,X9] :
                      ( X5 = X7
                      | k4_mcart_1(X6,X7,X8,X9) != X4 )
                  | k9_mcart_1(X0,X1,X2,X3,X4) != X5 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
              <=> ! [X6,X7,X8,X9] :
                    ( X5 = X7
                    | k4_mcart_1(X6,X7,X8,X9) != X4 ) )
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( k9_mcart_1(X0,X1,X2,X3,X4) = X5
                  <=> ! [X6,X7,X8,X9] :
                        ( k4_mcart_1(X6,X7,X8,X9) = X4
                       => X5 = X7 ) ) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).

fof(f53,plain,
    ( m1_subset_1(sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f51,f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(sK11(X0,X1,X2,X3,X4),X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f89,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f87,f54])).

fof(f54,plain,
    ( m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f51,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(sK12(X0,X1,X2,X3,X4),X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f87,plain,
    ( ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f85,f55])).

fof(f55,plain,
    ( m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f51,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3,X4)
      | m1_subset_1(sK13(X0,X1,X2,X3,X4),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,
    ( ~ m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,
    ( m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f31,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | m1_subset_1(sK14(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,
    ( ~ m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1)
    | ~ m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( sK6 != sK6
    | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6)
    | ~ m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4)
    | ~ m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3)
    | ~ m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2)
    | ~ m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f32,f72])).

fof(f72,plain,
    ( sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(duplicate_literal_removal,[],[f69])).

fof(f69,plain,
    ( sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(superposition,[],[f56,f66])).

fof(f32,plain,(
    ! [X6,X8,X7,X9] :
      ( k4_mcart_1(X6,X7,X8,X9) != sK6
      | sK5 = X7
      | ~ m1_subset_1(X9,sK4)
      | ~ m1_subset_1(X8,sK3)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (19618)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.52  % (19620)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (19617)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (19645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (19617)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  fof(f175,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f174])).
% 0.20/0.53  fof(f174,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0),
% 0.20/0.53    inference(superposition,[],[f33,f169])).
% 0.20/0.53  fof(f169,plain,(
% 0.20/0.53    k1_xboole_0 = sK1),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f147])).
% 0.20/0.53  fof(f147,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1),
% 0.20/0.53    inference(superposition,[],[f34,f145])).
% 0.20/0.53  fof(f145,plain,(
% 0.20/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.20/0.53    inference(superposition,[],[f35,f124])).
% 0.20/0.53  fof(f124,plain,(
% 0.20/0.53    k1_xboole_0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f105])).
% 0.20/0.53  fof(f105,plain,(
% 0.20/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.20/0.53    inference(superposition,[],[f36,f99])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    k1_xboole_0 = sK4 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3),
% 0.20/0.53    inference(trivial_inequality_removal,[],[f97])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    sK5 != sK5 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(superposition,[],[f37,f92])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(resolution,[],[f89,f71])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f70])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(superposition,[],[f53,f66])).
% 0.20/0.53  fof(f66,plain,(
% 0.20/0.53    k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(resolution,[],[f65,f31])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK5 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK6 | ~m1_subset_1(X9,sK4)) | ~m1_subset_1(X8,sK3)) | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3))) => (sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6) & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (sK5 = X7 | k4_mcart_1(X6,X7,X8,X9) != sK6 | ~m1_subset_1(X9,sK4)) | ~m1_subset_1(X8,sK3)) | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) & m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3,X4,X5] : (k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.53    inference(flattening,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0,X1,X2,X3,X4,X5] : (((k9_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X7 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X7))))) => (k9_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).
% 0.20/0.53  fof(f65,plain,(
% 0.20/0.53    ~m1_subset_1(sK6,k4_zfmisc_1(sK1,sK2,sK3,sK4)) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)),
% 0.20/0.53    inference(resolution,[],[f64,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => m1_subset_1(k9_mcart_1(X0,X1,X2,X3,X4),X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.53    inference(duplicate_literal_removal,[],[f63])).
% 0.20/0.53  fof(f63,plain,(
% 0.20/0.53    ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | k9_mcart_1(sK1,sK2,sK3,sK4,sK6) = sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(resolution,[],[f61,f31])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK6,k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(k9_mcart_1(X0,X1,X2,X3,sK6),X1) | sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) = k9_mcart_1(X0,X1,X2,X3,sK6) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4) )),
% 0.20/0.53    inference(superposition,[],[f49,f56])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.53    inference(resolution,[],[f51,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0) )),
% 0.20/0.53    inference(cnf_transformation,[],[f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ! [X0,X1,X2,X3,X4] : ((((k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0 & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK12(X0,X1,X2,X3,X4),X3)) & m1_subset_1(sK11(X0,X1,X2,X3,X4),X4)) | ~sP0(X0,X1,X2,X3,X4))),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f24,f27,f26,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (k4_mcart_1(X1,X5,X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(X5,X4)) => (? [X6] : (? [X7] : (k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(sK11(X0,X1,X2,X3,X4),X4)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) => (? [X7] : (k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(sK12(X0,X1,X2,X3,X4),X3)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    ! [X4,X3,X2,X1,X0] : (? [X7] : (k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),X7) = X0 & m1_subset_1(X7,X2)) => (k4_mcart_1(X1,sK11(X0,X1,X2,X3,X4),sK12(X0,X1,X2,X3,X4),sK13(X0,X1,X2,X3,X4)) = X0 & m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.54  % (19628)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (19621)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (19619)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (19639)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.55  % (19636)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.55  % (19631)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.55  % (19630)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.55  % (19626)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (19642)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (k4_mcart_1(X1,X5,X6,X7) = X0 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X3)) & m1_subset_1(X5,X4)) | ~sP0(X0,X1,X2,X3,X4))),
% 0.20/0.56    inference(rectify,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X4,X5,X3,X2,X1] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) | ~sP0(X4,X5,X3,X2,X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X4,X5,X3,X2,X1] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) | ~sP0(X4,X5,X3,X2,X1))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    sP0(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(resolution,[],[f31,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1) & m1_subset_1(sK14(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f16,f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X4,X3,X2,X1,X0] : (? [X5] : (sP0(X4,X5,X3,X2,X1) & m1_subset_1(X5,X0)) => (sP0(X4,sK14(X0,X1,X2,X3,X4),X3,X2,X1) & m1_subset_1(sK14(X0,X1,X2,X3,X4),X0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (sP0(X4,X5,X3,X2,X1) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(definition_folding,[],[f14,f15])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ( ! [X2,X0,X12,X10,X3,X1,X13,X11] : (~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | ~m1_subset_1(k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)),X1) | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) = X11 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(equality_resolution,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k9_mcart_1(X0,X1,X2,X3,k4_mcart_1(X10,X11,X12,X13)) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(k4_mcart_1(X10,X11,X12,X13),k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(equality_resolution,[],[f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X12,X10,X5,X3,X1,X13,X11] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4 | k9_mcart_1(X0,X1,X2,X3,X4) != X5 | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | (sK8(X4,X5) != X5 & k4_mcart_1(sK7(X4,X5),sK8(X4,X5),sK9(X4,X5),sK10(X4,X5)) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10])],[f20,f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X5,X4] : (? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4) => (sK8(X4,X5) != X5 & k4_mcart_1(sK7(X4,X5),sK8(X4,X5),sK9(X4,X5),sK10(X4,X5)) = X4))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X10,X11,X12,X13] : (X5 = X11 | k4_mcart_1(X10,X11,X12,X13) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(rectify,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : (((k9_mcart_1(X0,X1,X2,X3,X4) = X5 | ? [X6,X7,X8,X9] : (X5 != X7 & k4_mcart_1(X6,X7,X8,X9) = X4)) & (! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4) | k9_mcart_1(X0,X1,X2,X3,X4) != X5)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(nnf_transformation,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (! [X4] : (! [X5] : ((k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (X5 = X7 | k4_mcart_1(X6,X7,X8,X9) != X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ! [X5] : (m1_subset_1(X5,X1) => (k9_mcart_1(X0,X1,X2,X3,X4) = X5 <=> ! [X6,X7,X8,X9] : (k4_mcart_1(X6,X7,X8,X9) = X4 => X5 = X7)))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_mcart_1)).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    m1_subset_1(sK11(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(resolution,[],[f51,f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | m1_subset_1(sK11(X0,X1,X2,X3,X4),X4)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f89,plain,(
% 0.20/0.56    ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f88])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(resolution,[],[f87,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(resolution,[],[f51,f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | m1_subset_1(sK12(X0,X1,X2,X3,X4),X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(resolution,[],[f85,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(resolution,[],[f51,f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3,X4) | m1_subset_1(sK13(X0,X1,X2,X3,X4),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ~m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    ~m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(resolution,[],[f79,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.20/0.56    inference(resolution,[],[f31,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | m1_subset_1(sK14(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ~m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1) | ~m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(trivial_inequality_removal,[],[f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    sK6 != sK6 | sK5 = k9_mcart_1(sK1,sK2,sK3,sK4,sK6) | ~m1_subset_1(sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK4) | ~m1_subset_1(sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK3) | ~m1_subset_1(k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK2) | ~m1_subset_1(sK14(sK1,sK2,sK3,sK4,sK6),sK1) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(superposition,[],[f32,f72])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f69])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    sK6 = k4_mcart_1(sK14(sK1,sK2,sK3,sK4,sK6),k9_mcart_1(sK1,sK2,sK3,sK4,sK6),sK12(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2),sK13(sK6,sK14(sK1,sK2,sK3,sK4,sK6),sK4,sK3,sK2)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK4),
% 0.20/0.56    inference(superposition,[],[f56,f66])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X9] : (k4_mcart_1(X6,X7,X8,X9) != sK6 | sK5 = X7 | ~m1_subset_1(X9,sK4) | ~m1_subset_1(X8,sK3) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    sK5 != k9_mcart_1(sK1,sK2,sK3,sK4,sK6)),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    k1_xboole_0 != sK4),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    k1_xboole_0 != sK3),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    k1_xboole_0 != sK2),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    k1_xboole_0 != sK1),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (19617)------------------------------
% 0.20/0.56  % (19617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (19617)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (19617)Memory used [KB]: 1918
% 0.20/0.56  % (19617)Time elapsed: 0.114 s
% 0.20/0.56  % (19617)------------------------------
% 0.20/0.56  % (19617)------------------------------
% 0.20/0.56  % (19613)Success in time 0.199 s
%------------------------------------------------------------------------------
