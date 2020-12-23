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
% DateTime   : Thu Dec  3 12:59:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   77 (1217 expanded)
%              Number of leaves         :    6 ( 250 expanded)
%              Depth                    :   25
%              Number of atoms          :  326 (7559 expanded)
%              Number of equality atoms :  240 (4869 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(subsumption_resolution,[],[f162,f160])).

fof(f160,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f111,f111])).

fof(f111,plain,(
    ! [X0] : k1_mcart_1(k1_mcart_1(sK4)) = X0 ),
    inference(subsumption_resolution,[],[f110,f20])).

fof(f20,plain,(
    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k6_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X6
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X6 ) ) ) )
         => ( k6_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X6 ) ) ) )
       => ( k6_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

fof(f110,plain,(
    ! [X0] :
      ( sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f109,f19])).

fof(f19,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f109,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f108,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f108,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(subsumption_resolution,[],[f107,f17])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(resolution,[],[f100,f34])).

fof(f34,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f16,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f16,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f100,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7))
      | k1_xboole_0 = X5
      | k1_xboole_0 = X6
      | k1_xboole_0 = X7
      | sK3 = k6_mcart_1(X5,X6,X7,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X4 ) ),
    inference(superposition,[],[f48,f98])).

fof(f98,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK3),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK3),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_mcart_1(k1_mcart_1(sK4)) = X0
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(superposition,[],[f82,f94])).

fof(f94,plain,(
    ! [X12] :
      ( sK3 = sK6(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f93,f67])).

fof(f67,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f66,f62])).

fof(f62,plain,(
    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f61,f17])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f60,f19])).

fof(f60,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(subsumption_resolution,[],[f59,f18])).

fof(f59,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK0
    | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(resolution,[],[f38,f34])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f65,f19])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f64,f18])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f63,f17])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f42,f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f33,f22])).

% (5896)Refutation not found, incomplete strategy% (5896)------------------------------
% (5896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5896)Termination reason: Refutation not found, incomplete strategy

% (5896)Memory used [KB]: 10618
% (5896)Time elapsed: 0.123 s
% (5896)------------------------------
% (5896)------------------------------
% (5908)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (5903)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (5884)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (5879)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (5879)Refutation not found, incomplete strategy% (5879)------------------------------
% (5879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5879)Termination reason: Refutation not found, incomplete strategy

% (5879)Memory used [KB]: 1663
% (5879)Time elapsed: 0.132 s
% (5879)------------------------------
% (5879)------------------------------
% (5906)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (5900)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (5897)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

fof(f93,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK6(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f92,f77])).

fof(f77,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f76,f62])).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f75,f19])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f74,f18])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f73,f17])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f46,f34])).

% (5891)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f29,f22])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK6(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(subsumption_resolution,[],[f91,f72])).

fof(f72,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f71,f62])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f70,f19])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f69,f18])).

% (5887)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (5898)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (5894)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (5902)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f69,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f68,f17])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f43,f34])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f32,f22])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X12] :
      ( ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK6(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,(
    ! [X12] :
      ( sK4 != sK4
      | ~ m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1)
      | ~ m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2)
      | ~ m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0)
      | sK3 = sK6(sK0,sK1,sK2,X12,sK4)
      | k1_mcart_1(k1_mcart_1(sK4)) = X12 ) ),
    inference(superposition,[],[f35,f82])).

fof(f35,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X5,sK0)
      | sK3 = X6 ) ),
    inference(definition_unfolding,[],[f15,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f15,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X7,sK2)
      | k3_mcart_1(X5,X6,X7) != sK4
      | sK3 = X6 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f82,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_mcart_1(k1_mcart_1(sK4)) = X0 ) ),
    inference(forward_demodulation,[],[f81,f62])).

% (5894)Refutation not found, incomplete strategy% (5894)------------------------------
% (5894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5894)Termination reason: Refutation not found, incomplete strategy

% (5894)Memory used [KB]: 6140
% (5894)Time elapsed: 0.003 s
% (5894)------------------------------
% (5894)------------------------------
fof(f81,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f80,f19])).

fof(f80,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f79,f18])).

fof(f79,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(subsumption_resolution,[],[f78,f17])).

fof(f78,plain,(
    ! [X0] :
      ( sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k5_mcart_1(sK0,sK1,sK2,sK4) = X0 ) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(definition_unfolding,[],[f30,f22,f21])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
      | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k5_mcart_1(X0,X1,X2,X4) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

% (5892)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X1] :
      ( ~ m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k4_tarski(k4_tarski(X4,X5),X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
    inference(definition_unfolding,[],[f27,f22,f21])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k3_mcart_1(X4,X5,X6) != X3
      | k6_mcart_1(X0,X1,X2,X3) = X5 ) ),
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
    inference(ennf_transformation,[],[f4])).

% (5889)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

fof(f162,plain,(
    sK3 != k1_mcart_1(k1_mcart_1(sK4)) ),
    inference(superposition,[],[f20,f111])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (5896)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (5899)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (5907)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (5886)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (5880)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (5885)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (5882)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (5885)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (5905)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (5881)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f160])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X0,X1] : (X0 = X1) )),
% 0.21/0.54    inference(superposition,[],[f111,f111])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    ( ! [X0] : (k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f110,f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    sK3 != k6_mcart_1(sK0,sK1,sK2,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X6 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.54    inference(flattening,[],[f8])).
% 0.21/0.54  fof(f8,plain,(
% 0.21/0.54    ? [X0,X1,X2,X3,X4] : (((k6_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X6 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f6])).
% 0.21/0.54  fof(f6,conjecture,(
% 0.21/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X6)))) => (k6_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).
% 0.21/0.54  fof(f110,plain,(
% 0.21/0.54    ( ! [X0] : (sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f109,f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    k1_xboole_0 != sK2),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = sK2 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f108,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    k1_xboole_0 != sK1),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f107,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    k1_xboole_0 != sK0),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | sK3 = k6_mcart_1(sK0,sK1,sK2,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(resolution,[],[f100,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.21/0.54    inference(definition_unfolding,[],[f16,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X5,X6),X7)) | k1_xboole_0 = X5 | k1_xboole_0 = X6 | k1_xboole_0 = X7 | sK3 = k6_mcart_1(X5,X6,X7,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X4) )),
% 0.21/0.54    inference(superposition,[],[f48,f98])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK3),sK7(sK0,sK1,sK2,X0,sK4)) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f95])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK3),sK7(sK0,sK1,sK2,X0,sK4)) | k1_mcart_1(k1_mcart_1(sK4)) = X0 | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(superposition,[],[f82,f94])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X12] : (sK3 = sK6(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f93,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 0.21/0.54    inference(forward_demodulation,[],[f66,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f61,f17])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f60,f19])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(subsumption_resolution,[],[f59,f18])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK0 | k5_mcart_1(sK0,sK1,sK2,sK4) = k1_mcart_1(k1_mcart_1(sK4))),
% 0.21/0.54    inference(resolution,[],[f38,f34])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X0 | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f22])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f65,f19])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f64,f18])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f63,f17])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK0,sK1,sK2,X0,sK4),sK0) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 0.21/0.54    inference(resolution,[],[f42,f34])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 0.21/0.54    inference(definition_unfolding,[],[f33,f22])).
% 0.21/0.54  % (5896)Refutation not found, incomplete strategy% (5896)------------------------------
% 0.21/0.54  % (5896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5896)Memory used [KB]: 10618
% 0.21/0.54  % (5896)Time elapsed: 0.123 s
% 0.21/0.54  % (5896)------------------------------
% 0.21/0.54  % (5896)------------------------------
% 0.21/0.54  % (5908)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (5903)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (5884)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.42/0.54  % (5879)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.42/0.54  % (5879)Refutation not found, incomplete strategy% (5879)------------------------------
% 1.42/0.54  % (5879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (5879)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (5879)Memory used [KB]: 1663
% 1.42/0.54  % (5879)Time elapsed: 0.132 s
% 1.42/0.54  % (5879)------------------------------
% 1.42/0.54  % (5879)------------------------------
% 1.42/0.54  % (5906)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.54  % (5900)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK5(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.54    inference(cnf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ? [X5] : (? [X6] : (? [X7] : (X3 != X5 & k3_mcart_1(X5,X6,X7) = X4 & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.54    inference(flattening,[],[f13])).
% 1.42/0.54  fof(f13,plain,(
% 1.42/0.54    ! [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ? [X5] : (? [X6] : (? [X7] : ((X3 != X5 & k3_mcart_1(X5,X6,X7) = X4) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0))) | ~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.54    inference(ennf_transformation,[],[f5])).
% 1.42/0.55  % (5897)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.55  fof(f5,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).
% 1.42/0.55  fof(f93,plain,(
% 1.42/0.55    ( ! [X12] : (~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK6(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f92,f77])).
% 1.42/0.55  fof(f77,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 1.42/0.55    inference(forward_demodulation,[],[f76,f62])).
% 1.42/0.55  fof(f76,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f75,f19])).
% 1.42/0.55  fof(f75,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f74,f18])).
% 1.42/0.55  fof(f74,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f73,f17])).
% 1.42/0.55  fof(f73,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK7(sK0,sK1,sK2,X0,sK4),sK2) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(resolution,[],[f46,f34])).
% 1.42/0.55  % (5891)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.55  fof(f46,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(definition_unfolding,[],[f29,f22])).
% 1.42/0.55  fof(f29,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK7(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f92,plain,(
% 1.42/0.55    ( ! [X12] : (~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK6(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f91,f72])).
% 1.42/0.55  fof(f72,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 1.42/0.55    inference(forward_demodulation,[],[f71,f62])).
% 1.42/0.55  fof(f71,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f70,f19])).
% 1.42/0.55  fof(f70,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f69,f18])).
% 1.42/0.55  % (5887)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.42/0.55  % (5898)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (5894)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (5902)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.55  fof(f69,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f68,f17])).
% 1.42/0.55  fof(f68,plain,(
% 1.42/0.55    ( ! [X0] : (m1_subset_1(sK6(sK0,sK1,sK2,X0,sK4),sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(resolution,[],[f43,f34])).
% 1.42/0.55  fof(f43,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(definition_unfolding,[],[f32,f22])).
% 1.42/0.55  fof(f32,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | m1_subset_1(sK6(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  fof(f91,plain,(
% 1.42/0.55    ( ! [X12] : (~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK6(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 1.42/0.55    inference(trivial_inequality_removal,[],[f86])).
% 1.42/0.55  fof(f86,plain,(
% 1.42/0.55    ( ! [X12] : (sK4 != sK4 | ~m1_subset_1(sK6(sK0,sK1,sK2,X12,sK4),sK1) | ~m1_subset_1(sK7(sK0,sK1,sK2,X12,sK4),sK2) | ~m1_subset_1(sK5(sK0,sK1,sK2,X12,sK4),sK0) | sK3 = sK6(sK0,sK1,sK2,X12,sK4) | k1_mcart_1(k1_mcart_1(sK4)) = X12) )),
% 1.42/0.55    inference(superposition,[],[f35,f82])).
% 1.42/0.55  fof(f35,plain,(
% 1.42/0.55    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X5,sK0) | sK3 = X6) )),
% 1.42/0.55    inference(definition_unfolding,[],[f15,f21])).
% 1.42/0.55  fof(f21,plain,(
% 1.42/0.55    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.42/0.55    inference(cnf_transformation,[],[f1])).
% 1.42/0.55  fof(f1,axiom,(
% 1.42/0.55    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.42/0.55  fof(f15,plain,(
% 1.42/0.55    ( ! [X6,X7,X5] : (~m1_subset_1(X5,sK0) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X7,sK2) | k3_mcart_1(X5,X6,X7) != sK4 | sK3 = X6) )),
% 1.42/0.55    inference(cnf_transformation,[],[f9])).
% 1.42/0.55  fof(f82,plain,(
% 1.42/0.55    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_mcart_1(k1_mcart_1(sK4)) = X0) )),
% 1.42/0.55    inference(forward_demodulation,[],[f81,f62])).
% 1.42/0.55  % (5894)Refutation not found, incomplete strategy% (5894)------------------------------
% 1.42/0.55  % (5894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (5894)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (5894)Memory used [KB]: 6140
% 1.42/0.55  % (5894)Time elapsed: 0.003 s
% 1.42/0.55  % (5894)------------------------------
% 1.42/0.55  % (5894)------------------------------
% 1.42/0.55  fof(f81,plain,(
% 1.42/0.55    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f80,f19])).
% 1.42/0.55  fof(f80,plain,(
% 1.42/0.55    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f79,f18])).
% 1.42/0.55  fof(f79,plain,(
% 1.42/0.55    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(subsumption_resolution,[],[f78,f17])).
% 1.42/0.55  fof(f78,plain,(
% 1.42/0.55    ( ! [X0] : (sK4 = k4_tarski(k4_tarski(sK5(sK0,sK1,sK2,X0,sK4),sK6(sK0,sK1,sK2,X0,sK4)),sK7(sK0,sK1,sK2,X0,sK4)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k5_mcart_1(sK0,sK1,sK2,sK4) = X0) )),
% 1.42/0.55    inference(resolution,[],[f45,f34])).
% 1.42/0.55  fof(f45,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k4_tarski(k4_tarski(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4)),sK7(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(definition_unfolding,[],[f30,f22,f21])).
% 1.42/0.55  fof(f30,plain,(
% 1.42/0.55    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) | k3_mcart_1(sK5(X0,X1,X2,X3,X4),sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k5_mcart_1(X0,X1,X2,X4) = X3) )),
% 1.42/0.55    inference(cnf_transformation,[],[f14])).
% 1.42/0.55  % (5892)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.42/0.55  fof(f48,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X1] : (~m1_subset_1(k4_tarski(k4_tarski(X4,X5),X6),k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k6_mcart_1(X0,X1,X2,k4_tarski(k4_tarski(X4,X5),X6)) = X5) )),
% 1.42/0.55    inference(equality_resolution,[],[f40])).
% 1.42/0.55  fof(f40,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k4_tarski(k4_tarski(X4,X5),X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 1.42/0.55    inference(definition_unfolding,[],[f27,f22,f21])).
% 1.42/0.55  fof(f27,plain,(
% 1.42/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k3_mcart_1(X4,X5,X6) != X3 | k6_mcart_1(X0,X1,X2,X3) = X5) )),
% 1.42/0.55    inference(cnf_transformation,[],[f12])).
% 1.42/0.55  fof(f12,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : (! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.55    inference(flattening,[],[f11])).
% 1.42/0.55  fof(f11,plain,(
% 1.42/0.55    ! [X0,X1,X2,X3] : ((! [X4,X5,X6] : ((k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) | k3_mcart_1(X4,X5,X6) != X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)))),
% 1.42/0.55    inference(ennf_transformation,[],[f4])).
% 1.42/0.55  % (5889)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.55  fof(f4,axiom,(
% 1.42/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => ~(? [X4,X5,X6] : (~(k7_mcart_1(X0,X1,X2,X3) = X6 & k6_mcart_1(X0,X1,X2,X3) = X5 & k5_mcart_1(X0,X1,X2,X3) = X4) & k3_mcart_1(X4,X5,X6) = X3) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.42/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).
% 1.42/0.55  fof(f162,plain,(
% 1.42/0.55    sK3 != k1_mcart_1(k1_mcart_1(sK4))),
% 1.42/0.55    inference(superposition,[],[f20,f111])).
% 1.42/0.55  % SZS output end Proof for theBenchmark
% 1.42/0.55  % (5885)------------------------------
% 1.42/0.55  % (5885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (5885)Termination reason: Refutation
% 1.42/0.55  
% 1.42/0.55  % (5885)Memory used [KB]: 6268
% 1.42/0.55  % (5885)Time elapsed: 0.117 s
% 1.42/0.55  % (5885)------------------------------
% 1.42/0.55  % (5885)------------------------------
% 1.42/0.56  % (5878)Success in time 0.195 s
%------------------------------------------------------------------------------
