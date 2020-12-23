%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 512 expanded)
%              Number of leaves         :    9 ( 136 expanded)
%              Depth                    :   24
%              Number of atoms          :  377 (4558 expanded)
%              Number of equality atoms :  272 (2829 expanded)
%              Maximal formula depth    :   20 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f115,plain,(
    $false ),
    inference(subsumption_resolution,[],[f64,f114])).

fof(f114,plain,(
    ! [X0] : k1_mcart_1(k1_mcart_1(sK4)) = X0 ),
    inference(subsumption_resolution,[],[f113,f28])).

fof(f28,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f17])).

% (20320)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f17,plain,
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

% (20301)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (20322)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (20324)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (20319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (20309)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (20329)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (20318)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (20309)Refutation not found, incomplete strategy% (20309)------------------------------
% (20309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20309)Termination reason: Refutation not found, incomplete strategy

% (20309)Memory used [KB]: 10874
% (20309)Time elapsed: 0.127 s
% (20309)------------------------------
% (20309)------------------------------
% (20312)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (20321)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20306)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (20325)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (20314)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (20313)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (20327)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f113,plain,(
    ! [X0] :
      ( sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f112,f25])).

fof(f25,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f111,f26])).

fof(f26,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f110,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(resolution,[],[f108,f23])).

fof(f23,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(sK4,k3_zfmisc_1(X9,X10,X11))
      | k1_xboole_0 = X11
      | k1_xboole_0 = X10
      | k1_xboole_0 = X9
      | sK3 = k7_mcart_1(X9,X10,X11,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X8 ) ),
    inference(superposition,[],[f43,f105])).

fof(f105,plain,(
    ! [X0] :
      ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK3)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK3)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(superposition,[],[f93,f101])).

fof(f101,plain,(
    ! [X12] :
      ( sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f100,f78])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f77,f59])).

fof(f59,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f58,f25])).

fof(f58,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f56,f27])).

fof(f56,plain,
    ( k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f40,f23])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f76,f25])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f75,f26])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f27])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f35,f23])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ( sK5(X0,X1,X2,X3,X4) != X3
        & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f15,f21,f20,f19])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
     => ( ? [X6] :
            ( ? [X7] :
                ( sK5(X0,X1,X2,X3,X4) != X3
                & k3_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7) = X4
                & m1_subset_1(X7,X2) )
            & m1_subset_1(X6,X1) )
        & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) ) ) ),
    introduced(choice_axiom,[])).

% (20310)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f20,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ? [X7] :
              ( sK5(X0,X1,X2,X3,X4) != X3
              & k3_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7) = X4
              & m1_subset_1(X7,X2) )
          & m1_subset_1(X6,X1) )
     => ( ? [X7] :
            ( sK5(X0,X1,X2,X3,X4) != X3
            & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7) = X4
            & m1_subset_1(X7,X2) )
        & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( sK5(X0,X1,X2,X3,X4) != X3
          & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7) = X4
          & m1_subset_1(X7,X2) )
     => ( sK5(X0,X1,X2,X3,X4) != X3
        & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
        & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( X3 != X5
                  & k3_mcart_1(X5,X6,X7) = X4
                  & m1_subset_1(X7,X2) )
              & m1_subset_1(X6,X1) )
          & m1_subset_1(X5,X0) )
      | ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X5 ) ) ) )
       => ( k5_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f100,plain,(
    ! [X12] :
      ( sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f99,f83])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f82,f59])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f27])).

fof(f79,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f99,plain,(
    ! [X12] :
      ( sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f98,f88])).

fof(f88,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f87,f59])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f86,f25])).

fof(f86,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f85,f26])).

fof(f85,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f84,f27])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f37,f23])).

fof(f37,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X12] :
      ( sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,(
    ! [X12] :
      ( sK4 != sK4
      | sK3 = sK7(sK0,sK1,sK2,X12,sK4)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(superposition,[],[f24,f93])).

fof(f24,plain,(
    ! [X6,X7,X5] :
      ( k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,(
    ! [X0] :
      ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f92,f59])).

fof(f92,plain,(
    ! [X0] :
      ( sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4))
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4))
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f90,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4))
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f89,f27])).

fof(f89,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4))
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f38,f23])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = X6
      | k3_mcart_1(X4,X5,X6) != X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f64,plain,(
    sK4 != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f63,f25])).

fof(f63,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f62,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f61,f27])).

fof(f61,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK4))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f60,f23])).

fof(f60,plain,
    ( sK4 != k1_mcart_1(k1_mcart_1(sK4))
    | ~ m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f32,f59])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X0,X1,X2,X3) != X3
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) != X3
            & k6_mcart_1(X0,X1,X2,X3) != X3
            & k5_mcart_1(X0,X1,X2,X3) != X3 )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) != X3
                & k6_mcart_1(X0,X1,X2,X3) != X3
                & k5_mcart_1(X0,X1,X2,X3) != X3 ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (20323)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (20300)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (20303)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20316)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (20300)Refutation not found, incomplete strategy% (20300)------------------------------
% 0.21/0.52  % (20300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (20308)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (20315)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (20311)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (20300)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20300)Memory used [KB]: 1791
% 0.21/0.53  % (20300)Time elapsed: 0.104 s
% 0.21/0.53  % (20300)------------------------------
% 0.21/0.53  % (20300)------------------------------
% 0.21/0.53  % (20304)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (20307)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (20305)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (20302)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20305)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f64,f114])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    ( ! [X0] : (k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f113,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f17])).
% 0.21/0.54  % (20320)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (20301)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (20322)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (20324)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (20319)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (20309)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (20329)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (20318)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (20309)Refutation not found, incomplete strategy% (20309)------------------------------
% 0.21/0.55  % (20309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20309)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20309)Memory used [KB]: 10874
% 0.21/0.55  % (20309)Time elapsed: 0.127 s
% 0.21/0.55  % (20309)------------------------------
% 0.21/0.55  % (20309)------------------------------
% 0.21/0.55  % (20312)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (20321)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (20306)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (20325)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (20314)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (20313)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (20327)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(flattening,[],[f9])).
% 0.21/0.56  fof(f9,plain,(
% 0.21/0.56    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.56    inference(negated_conjecture,[],[f7])).
% 0.21/0.56  fof(f7,conjecture,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    ( ! [X0] : (sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f112,f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    k1_xboole_0 != sK0),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f111,f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    k1_xboole_0 != sK1),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f110,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    k1_xboole_0 != sK2),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK3 = k7_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(resolution,[],[f108,f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    ( ! [X10,X8,X11,X9] : (~m1_subset_1(sK4,k3_zfmisc_1(X9,X10,X11)) | k1_xboole_0 = X11 | k1_xboole_0 = X10 | k1_xboole_0 = X9 | sK3 = k7_mcart_1(X9,X10,X11,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X8) )),
% 0.21/0.56    inference(superposition,[],[f43,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK3) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK3) | k1_mcart_1(k1_mcart_1(sK4)) = X0 | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(superposition,[],[f93,f101])).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ( ! [X12] : (sK3 = sK7(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f100,f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f77,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f58,f25])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f56,f27])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(resolution,[],[f40,f23])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f76,f25])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f75,f26])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f74,f27])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(resolution,[],[f35,f23])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | (((sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f15,f21,f20,f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X4,X3,X2,X1,X0] : (? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) => (? [X6] : (? [X7] : (sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (20310)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X4,X3,X2,X1,X0] : (? [X6] : (? [X7] : (sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) => (? [X7] : (sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X4,X3,X2,X1,X0] : (? [X7] : (sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),X7) = X4 & m1_subset_1(X7,X2)) => (sK5(X0,X1,X2,X3,X4) != X3 & k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 & m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X5] : (? [X6] : (? [X7] : ((X3 != X5 & k3_mcart_1(X5,X6,X7) = X4) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    ( ! [X12] : (sK3 = sK7(sK0,sK1,sK2,X12,sK4) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f99,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f82,f59])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f81,f25])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f80,f26])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f79,f27])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(resolution,[],[f36,f23])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    ( ! [X12] : (sK3 = sK7(sK0,sK1,sK2,X12,sK4) | ~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f98,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f87,f59])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f86,f25])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f85,f26])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f84,f27])).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(resolution,[],[f37,f23])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ( ! [X12] : (sK3 = sK7(sK0,sK1,sK2,X12,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.56    inference(trivial_inequality_removal,[],[f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X12] : (sK4 != sK4 | sK3 = sK7(sK0,sK1,sK2,X12,sK4) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.56    inference(superposition,[],[f24,f93])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ( ! [X6,X7,X5] : (k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4)) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.56    inference(forward_demodulation,[],[f92,f59])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0] : (sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4)) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f91,f25])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4)) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f90,f26])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4)) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(subsumption_resolution,[],[f89,f27])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0] : (k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK4 = k3_mcart_1(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4),sK7(sK0,sK1,sK2,X0,sK4)) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.56    inference(resolution,[],[f38,f23])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k3_mcart_1(X4,X5,X6),k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k7_mcart_1(X0,X1,X2,k3_mcart_1(X4,X5,X6)) = X6) )),
% 0.21/0.56    inference(equality_resolution,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = X6 | k3_mcart_1(X4,X5,X6) != X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_mcart_1)).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    sK4 != k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.56    inference(subsumption_resolution,[],[f63,f25])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    sK4 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f62,f26])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    sK4 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f61,f27])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    sK4 != k1_mcart_1(k1_mcart_1(sK4)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(subsumption_resolution,[],[f60,f23])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    sK4 != k1_mcart_1(k1_mcart_1(sK4)) | ~m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.21/0.56    inference(superposition,[],[f32,f59])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X0,X1,X2,X3) != X3 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) != X3 & k6_mcart_1(X0,X1,X2,X3) != X3 & k5_mcart_1(X0,X1,X2,X3) != X3)) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_mcart_1)).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20305)------------------------------
% 0.21/0.56  % (20305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20305)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20305)Memory used [KB]: 6268
% 0.21/0.56  % (20305)Time elapsed: 0.118 s
% 0.21/0.56  % (20305)------------------------------
% 0.21/0.56  % (20305)------------------------------
% 0.21/0.56  % (20317)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (20299)Success in time 0.197 s
%------------------------------------------------------------------------------
