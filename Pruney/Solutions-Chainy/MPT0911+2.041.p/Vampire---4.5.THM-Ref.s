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
% DateTime   : Thu Dec  3 12:59:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 410 expanded)
%              Number of leaves         :    7 ( 115 expanded)
%              Depth                    :   36
%              Number of atoms          :  300 (3577 expanded)
%              Number of equality atoms :  202 (2166 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f11])).

% (2614)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f11,plain,
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
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f88,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f87,f20])).

fof(f20,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f87,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f86,f21])).

fof(f21,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f22,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,
    ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f75,f17])).

fof(f17,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8))
      | sK3 = k7_mcart_1(X6,X7,X8,sK4)
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6 ) ),
    inference(backward_demodulation,[],[f42,f72])).

fof(f72,plain,(
    sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f71,f19])).

% (2613)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (2612)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f71,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f70,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f69,f21])).

% (2615)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f69,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f67,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),X1)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
            & m1_subset_1(sK7(X0,X1,X2,X3),X2)
            & m1_subset_1(sK6(X0,X1,X2,X3),X1)
            & m1_subset_1(sK5(X0,X1,X2,X3),X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f15,f14,f13])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( k3_mcart_1(X4,X5,X6) = X3
                  & m1_subset_1(X6,X2) )
              & m1_subset_1(X5,X1) )
          & m1_subset_1(X4,X0) )
     => ( ? [X5] :
            ( ? [X6] :
                ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
                & m1_subset_1(X6,X2) )
            & m1_subset_1(X5,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3
              & m1_subset_1(X6,X2) )
          & m1_subset_1(X5,X1) )
     => ( ? [X6] :
            ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
            & m1_subset_1(X6,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6] :
          ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3
          & m1_subset_1(X6,X2) )
     => ( k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
        & m1_subset_1(sK7(X0,X1,X2,X3),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( k3_mcart_1(X4,X5,X6) = X3
                      & m1_subset_1(X6,X2) )
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,X0) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ! [X6] :
                        ( m1_subset_1(X6,X2)
                       => k3_mcart_1(X4,X5,X6) != X3 ) ) )
            & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

fof(f67,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | sK3 = sK7(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f66,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f65,f20])).

fof(f65,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f64,f21])).

fof(f64,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f63,f17])).

fof(f63,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f57,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3),X2)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(subsumption_resolution,[],[f49,f56])).

fof(f56,plain,(
    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) ),
    inference(subsumption_resolution,[],[f55,f19])).

fof(f55,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f54,f20])).

fof(f54,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f53,f21])).

fof(f53,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f52,plain,
    ( m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f26,f48])).

fof(f48,plain,(
    sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f47,f19])).

fof(f47,plain,
    ( k1_xboole_0 = sK0
    | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f46,f20])).

fof(f46,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(resolution,[],[f40,f17])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(X0,X1,X2,sK4) ) ),
    inference(superposition,[],[f32,f39])).

fof(f39,plain,(
    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) ),
    inference(subsumption_resolution,[],[f38,f19])).

fof(f38,plain,
    ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f37,f20])).

fof(f37,plain,
    ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f33,f21])).

fof(f33,plain,
    ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f29,f17])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4 ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) = X4
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4,X5,X6] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = X6
            & k6_mcart_1(X0,X1,X2,X3) = X5
            & k5_mcart_1(X0,X1,X2,X3) = X4 )
          | k3_mcart_1(X4,X5,X6) != X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
     => ~ ( ? [X4,X5,X6] :
              ( ~ ( k7_mcart_1(X0,X1,X2,X3) = X6
                  & k6_mcart_1(X0,X1,X2,X3) = X5
                  & k5_mcart_1(X0,X1,X2,X3) = X4 )
              & k3_mcart_1(X4,X5,X6) = X3 )
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,
    ( ~ m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)
    | sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) ),
    inference(backward_demodulation,[],[f44,f48])).

fof(f44,plain,
    ( sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(trivial_inequality_removal,[],[f43])).

fof(f43,plain,
    ( sK4 != sK4
    | sK3 = sK7(sK0,sK1,sK2,sK4)
    | ~ m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2)
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)
    | ~ m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0) ),
    inference(superposition,[],[f18,f39])).

fof(f18,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X6,X8,X7] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8))
      | k1_xboole_0 = X8
      | k1_xboole_0 = X7
      | k1_xboole_0 = X6
      | sK7(sK0,sK1,sK2,sK4) = k7_mcart_1(X6,X7,X8,sK4) ) ),
    inference(superposition,[],[f30,f39])).

fof(f30,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6 ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:13:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (2616)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (2616)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (2633)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (2625)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    k1_xboole_0 != sK0),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f7,f11])).
% 0.21/0.51  % (2614)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    k1_xboole_0 != sK1),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(resolution,[],[f75,f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8)) | sK3 = k7_mcart_1(X6,X7,X8,sK4) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6) )),
% 0.21/0.51    inference(backward_demodulation,[],[f42,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f71,f19])).
% 0.21/0.51  % (2613)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2612)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    sK3 = sK7(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f20])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    sK3 = sK7(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f69,f21])).
% 0.21/0.51  % (2615)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    sK3 = sK7(sK0,sK1,sK2,sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(subsumption_resolution,[],[f68,f17])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.51    inference(resolution,[],[f67,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3),X1) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (! [X3] : ((((k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f15,f14,f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X3,X2,X1,X0] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) => (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(sK5(X0,X1,X2,X3),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X3,X2,X1,X0] : (? [X5] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) => (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(sK6(X0,X1,X2,X3),X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X3,X2,X1,X0] : (? [X6] : (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),X6) = X3 & m1_subset_1(X6,X2)) => (k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 & m1_subset_1(sK7(X0,X1,X2,X3),X2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f10,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (! [X3] : (? [X4] : (? [X5] : (? [X6] : (k3_mcart_1(X4,X5,X6) = X3 & m1_subset_1(X6,X2)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(? [X3] : (! [X4] : (m1_subset_1(X4,X0) => ! [X5] : (m1_subset_1(X5,X1) => ! [X6] : (m1_subset_1(X6,X2) => k3_mcart_1(X4,X5,X6) != X3))) & m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | sK3 = sK7(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f19])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f65,f20])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f64,f21])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f63,f17])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f57,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3),X2) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.52    inference(subsumption_resolution,[],[f49,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f55,f19])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f54,f20])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f53,f21])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f52,f17])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(superposition,[],[f26,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f47,f19])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k1_xboole_0 = sK0 | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f46,f20])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f45,f21])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.52    inference(resolution,[],[f40,f17])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(sK4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK5(sK0,sK1,sK2,sK4) = k5_mcart_1(X0,X1,X2,sK4)) )),
% 0.21/0.52    inference(superposition,[],[f32,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4))),
% 0.21/0.52    inference(subsumption_resolution,[],[f38,f19])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f37,f20])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(subsumption_resolution,[],[f33,f21])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,sK4),sK6(sK0,sK1,sK2,sK4),sK7(sK0,sK1,sK2,sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.52    inference(resolution,[],[f29,f17])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3),sK6(X0,X1,X2,X3),sK7(X0,X1,X2,X3)) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X4) )),
% 0.21/0.52    inference(equality_resolution,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) = X4 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(flattening,[],[f8])).
% 0.21/0.52  fof(f8,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK5(X0,X1,X2,X3),X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ~m1_subset_1(k5_mcart_1(sK0,sK1,sK2,sK4),sK0) | sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1)),
% 0.21/0.52    inference(backward_demodulation,[],[f44,f48])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    sK4 != sK4 | sK3 = sK7(sK0,sK1,sK2,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,sK4),sK0)),
% 0.21/0.52    inference(superposition,[],[f18,f39])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f12])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X6,X8,X7] : (~m1_subset_1(sK4,k3_zfmisc_1(X6,X7,X8)) | k1_xboole_0 = X8 | k1_xboole_0 = X7 | k1_xboole_0 = X6 | sK7(sK0,sK1,sK2,sK4) = k7_mcart_1(X6,X7,X8,sK4)) )),
% 0.21/0.52    inference(superposition,[],[f30,f39])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6) )),
% 0.21/0.52    inference(equality_resolution,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2616)------------------------------
% 0.21/0.52  % (2616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2616)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2616)Memory used [KB]: 6268
% 0.21/0.52  % (2616)Time elapsed: 0.100 s
% 0.21/0.52  % (2616)------------------------------
% 0.21/0.52  % (2616)------------------------------
% 0.21/0.52  % (2610)Success in time 0.154 s
%------------------------------------------------------------------------------
