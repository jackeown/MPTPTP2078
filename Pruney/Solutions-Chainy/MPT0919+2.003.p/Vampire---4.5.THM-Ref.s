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
% DateTime   : Thu Dec  3 12:59:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 194 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   27
%              Number of atoms          :  370 (1485 expanded)
%              Number of equality atoms :  242 ( 897 expanded)
%              Maximal formula depth    :   23 (   9 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f145])).

% (634)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f145,plain,
    ( ~ spl10_5
    | spl10_4
    | spl10_3
    | spl10_2
    | spl10_1
    | spl10_6 ),
    inference(avatar_split_clause,[],[f137,f73,f48,f53,f58,f63,f68])).

fof(f68,plain,
    ( spl10_5
  <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f63,plain,
    ( spl10_4
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f58,plain,
    ( spl10_3
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f53,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f48,plain,
    ( spl10_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f73,plain,
    ( spl10_6
  <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f137,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | spl10_6 ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,
    ( sK4 != sK4
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | sK5 != sK5
    | spl10_6 ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,
    ( sK4 != sK4
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | ~ m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    | sK5 != sK5
    | spl10_6 ),
    inference(superposition,[],[f75,f122])).

fof(f122,plain,(
    ! [X30,X28,X31,X29,X27] :
      ( sK4 = k8_mcart_1(X28,X29,X30,X31,X27)
      | k1_xboole_0 = X28
      | k1_xboole_0 = X29
      | k1_xboole_0 = X30
      | k1_xboole_0 = X31
      | ~ m1_subset_1(X27,k4_zfmisc_1(X28,X29,X30,X31))
      | ~ m1_subset_1(X27,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | sK5 != X27 ) ),
    inference(superposition,[],[f46,f106])).

fof(f106,plain,(
    ! [X3] :
      ( k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | sK5 != X3 ) ),
    inference(global_subsumption,[],[f16,f17,f18,f19,f103])).

fof(f103,plain,(
    ! [X3] :
      ( k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | sK5 != X3 ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X3] :
      ( k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | sK5 != X3
      | ~ m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    inference(superposition,[],[f38,f97])).

fof(f97,plain,(
    ! [X0] :
      ( sK4 = sK6(sK0,sK1,sK2,sK3,X0)
      | sK5 != X0
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    inference(global_subsumption,[],[f16,f17,f18,f19,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sK5 != X0
      | sK4 = sK6(sK0,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( sK5 != X0
      | sK4 = sK6(sK0,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f94,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3,X4),X0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK5 != X0
      | sK4 = sK6(X1,sK1,sK2,sK3,X0)
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1 ) ),
    inference(global_subsumption,[],[f17,f18,f19,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK4 = sK6(X1,sK1,sK2,sK3,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK5 != X0
      | ~ m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0)
      | sK4 = sK6(X1,sK1,sK2,sK3,X0)
      | k1_xboole_0 = sK1
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f91,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK7(X0,X1,X2,X3,X4),X1)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

% (661)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (643)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK6(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f18,f19,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK6(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK3 ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1)
      | sK5 != X2
      | ~ m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0)
      | sK4 = sK6(X0,X1,sK2,sK3,X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | ~ m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f88,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X3,X4),X2)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK6(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(global_subsumption,[],[f19,f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK6(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2)
      | sK5 != X3
      | ~ m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0)
      | sK4 = sK6(X0,X1,X2,sK3,X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = sK3
      | ~ m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f80,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK9(X0,X1,X2,X3,X4),X3)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK9(X0,X1,X2,X3,X4),sK3)
      | ~ m1_subset_1(sK7(X0,X1,X2,X3,X4),sK1)
      | ~ m1_subset_1(sK8(X0,X1,X2,X3,X4),sK2)
      | sK5 != X4
      | ~ m1_subset_1(sK6(X0,X1,X2,X3,X4),sK0)
      | sK4 = sK6(X0,X1,X2,X3,X4)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f37,f38])).

fof(f37,plain,(
    ! [X6,X8,X7,X9] :
      ( sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | ~ m1_subset_1(X6,sK0)
      | sK4 = X6 ) ),
    inference(definition_unfolding,[],[f14,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f14,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(X6,sK0)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(X8,sK2)
      | ~ m1_subset_1(X9,sK3)
      | k4_mcart_1(X6,X7,X8,X9) != sK5
      | sK4 = X6 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( k8_mcart_1(X0,X1,X2,X3,X5) != X4
      & k1_xboole_0 != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X6] :
          ( ! [X7] :
              ( ! [X8] :
                  ( ! [X9] :
                      ( X4 = X6
                      | k4_mcart_1(X6,X7,X8,X9) != X5
                      | ~ m1_subset_1(X9,X3) )
                  | ~ m1_subset_1(X8,X2) )
              | ~ m1_subset_1(X7,X1) )
          | ~ m1_subset_1(X6,X0) )
      & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                           => X4 = X6 ) ) ) ) )
         => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
            | k1_xboole_0 = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                         => X4 = X6 ) ) ) ) )
       => ( k8_mcart_1(X0,X1,X2,X3,X5) = X4
          | k1_xboole_0 = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f28,f36])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f18,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    ! [X6,X2,X0,X8,X7,X5,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(definition_unfolding,[],[f32,f36])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2
      | k1_xboole_0 = X3
      | k4_mcart_1(X5,X6,X7,X8) != X4
      | k8_mcart_1(X0,X1,X2,X3,X4) = X5 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5,X6,X7,X8] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
            & k10_mcart_1(X0,X1,X2,X3,X4) = X7
            & k9_mcart_1(X0,X1,X2,X3,X4) = X6
            & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
          | k4_mcart_1(X5,X6,X7,X8) != X4 )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
     => ~ ( ? [X5,X6,X7,X8] :
              ( ~ ( k11_mcart_1(X0,X1,X2,X3,X4) = X8
                  & k10_mcart_1(X0,X1,X2,X3,X4) = X7
                  & k9_mcart_1(X0,X1,X2,X3,X4) = X6
                  & k8_mcart_1(X0,X1,X2,X3,X4) = X5 )
              & k4_mcart_1(X5,X6,X7,X8) = X4 )
          & k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

fof(f75,plain,
    ( sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)
    | spl10_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f76,plain,(
    ~ spl10_6 ),
    inference(avatar_split_clause,[],[f20,f73])).

fof(f20,plain,(
    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f15,f68])).

fof(f15,plain,(
    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ~ spl10_4 ),
    inference(avatar_split_clause,[],[f19,f63])).

fof(f61,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f18,f58])).

fof(f56,plain,(
    ~ spl10_2 ),
    inference(avatar_split_clause,[],[f17,f53])).

fof(f51,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f16,f48])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:52:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (672)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (662)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (642)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (638)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (637)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (633)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (679)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (672)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (678)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (635)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (673)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f146,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f51,f56,f61,f66,f71,f76,f145])).
% 0.20/0.54  % (634)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    ~spl10_5 | spl10_4 | spl10_3 | spl10_2 | spl10_1 | spl10_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f137,f73,f48,f53,f58,f63,f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    spl10_5 <=> m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    spl10_4 <=> k1_xboole_0 = sK3),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    spl10_3 <=> k1_xboole_0 = sK2),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    spl10_2 <=> k1_xboole_0 = sK1),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.20/0.54  fof(f48,plain,(
% 0.20/0.54    spl10_1 <=> k1_xboole_0 = sK0),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    spl10_6 <=> sK4 = k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | spl10_6),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | sK5 != sK5 | spl10_6),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f135])).
% 0.20/0.54  fof(f135,plain,(
% 0.20/0.54    sK4 != sK4 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | ~m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | sK5 != sK5 | spl10_6),
% 0.20/0.54    inference(superposition,[],[f75,f122])).
% 0.20/0.54  fof(f122,plain,(
% 0.20/0.54    ( ! [X30,X28,X31,X29,X27] : (sK4 = k8_mcart_1(X28,X29,X30,X31,X27) | k1_xboole_0 = X28 | k1_xboole_0 = X29 | k1_xboole_0 = X30 | k1_xboole_0 = X31 | ~m1_subset_1(X27,k4_zfmisc_1(X28,X29,X30,X31)) | ~m1_subset_1(X27,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | sK5 != X27) )),
% 0.20/0.54    inference(superposition,[],[f46,f106])).
% 0.20/0.54  fof(f106,plain,(
% 0.20/0.54    ( ! [X3] : (k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | sK5 != X3) )),
% 0.20/0.54    inference(global_subsumption,[],[f16,f17,f18,f19,f103])).
% 0.20/0.54  fof(f103,plain,(
% 0.20/0.54    ( ! [X3] : (k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | sK5 != X3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f100])).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X3] : (k4_tarski(k4_tarski(k4_tarski(sK4,sK7(sK0,sK1,sK2,sK3,X3)),sK8(sK0,sK1,sK2,sK3,X3)),sK9(sK0,sK1,sK2,sK3,X3)) = X3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | sK5 != X3 | ~m1_subset_1(X3,k4_zfmisc_1(sK0,sK1,sK2,sK3))) )),
% 0.20/0.54    inference(superposition,[],[f38,f97])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ( ! [X0] : (sK4 = sK6(sK0,sK1,sK2,sK3,X0) | sK5 != X0 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3))) )),
% 0.20/0.54    inference(global_subsumption,[],[f16,f17,f18,f19,f96])).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 != X0 | sK4 = sK6(sK0,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f95])).
% 0.20/0.54  fof(f95,plain,(
% 0.20/0.54    ( ! [X0] : (sK5 != X0 | sK4 = sK6(sK0,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X0,k4_zfmisc_1(sK0,sK1,sK2,sK3)) | k1_xboole_0 = sK0) )),
% 0.20/0.54    inference(resolution,[],[f94,f31])).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK6(X0,X1,X2,X3,X4),X0) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ! [X0,X1,X2,X3] : (! [X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (k4_mcart_1(X5,X6,X7,X8) = X4 & m1_subset_1(X8,X3)) & m1_subset_1(X7,X2)) & m1_subset_1(X6,X1)) & m1_subset_1(X5,X0)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2,X3] : ~(? [X4] : (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => ! [X8] : (m1_subset_1(X8,X3) => k4_mcart_1(X5,X6,X7,X8) != X4)))) & m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK5 != X0 | sK4 = sK6(X1,sK1,sK2,sK3,X0) | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1) )),
% 0.20/0.54    inference(global_subsumption,[],[f17,f18,f19,f93])).
% 0.20/0.54  fof(f93,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK4 = sK6(X1,sK1,sK2,sK3,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X0,X1] : (sK5 != X0 | ~m1_subset_1(sK6(X1,sK1,sK2,sK3,X0),sK0) | sK4 = sK6(X1,sK1,sK2,sK3,X0) | k1_xboole_0 = sK1 | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X0,k4_zfmisc_1(X1,sK1,sK2,sK3)) | k1_xboole_0 = X1) )),
% 0.20/0.54    inference(resolution,[],[f91,f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK7(X0,X1,X2,X3,X4),X1) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(cnf_transformation,[],[f11])).
% 0.20/0.54  % (661)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (643)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK6(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(global_subsumption,[],[f18,f19,f90])).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK6(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = sK3) )),
% 0.20/0.54    inference(duplicate_literal_removal,[],[f89])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK7(X0,X1,sK2,sK3,X2),sK1) | sK5 != X2 | ~m1_subset_1(sK6(X0,X1,sK2,sK3,X2),sK0) | sK4 = sK6(X0,X1,sK2,sK3,X2) | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | ~m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = sK2 | k1_xboole_0 = sK3 | ~m1_subset_1(X2,k4_zfmisc_1(X0,X1,sK2,sK3)) | k1_xboole_0 = X0) )),
% 0.20/0.54    inference(resolution,[],[f88,f29])).
% 1.41/0.54  fof(f29,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK8(X0,X1,X2,X3,X4),X2) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f11])).
% 1.41/0.54  fof(f88,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | ~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK6(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(global_subsumption,[],[f19,f87])).
% 1.41/0.54  fof(f87,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK6(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(duplicate_literal_removal,[],[f86])).
% 1.41/0.54  fof(f86,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK7(X0,X1,X2,sK3,X3),sK1) | ~m1_subset_1(sK8(X0,X1,X2,sK3,X3),sK2) | sK5 != X3 | ~m1_subset_1(sK6(X0,X1,X2,sK3,X3),sK0) | sK4 = sK6(X0,X1,X2,sK3,X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = sK3 | ~m1_subset_1(X3,k4_zfmisc_1(X0,X1,X2,sK3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(resolution,[],[f80,f27])).
% 1.41/0.54  fof(f27,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK9(X0,X1,X2,X3,X4),X3) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(cnf_transformation,[],[f11])).
% 1.41/0.54  fof(f80,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK9(X0,X1,X2,X3,X4),sK3) | ~m1_subset_1(sK7(X0,X1,X2,X3,X4),sK1) | ~m1_subset_1(sK8(X0,X1,X2,X3,X4),sK2) | sK5 != X4 | ~m1_subset_1(sK6(X0,X1,X2,X3,X4),sK0) | sK4 = sK6(X0,X1,X2,X3,X4) | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(superposition,[],[f37,f38])).
% 1.41/0.54  fof(f37,plain,(
% 1.41/0.54    ( ! [X6,X8,X7,X9] : (sK5 != k4_tarski(k4_tarski(k4_tarski(X6,X7),X8),X9) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | ~m1_subset_1(X6,sK0) | sK4 = X6) )),
% 1.41/0.54    inference(definition_unfolding,[],[f14,f36])).
% 1.41/0.54  fof(f36,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 1.41/0.54    inference(definition_unfolding,[],[f22,f21])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f1])).
% 1.41/0.54  fof(f1,axiom,(
% 1.41/0.54    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f2])).
% 1.41/0.54  fof(f2,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 1.41/0.54  fof(f14,plain,(
% 1.41/0.54    ( ! [X6,X8,X7,X9] : (~m1_subset_1(X6,sK0) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(X8,sK2) | ~m1_subset_1(X9,sK3) | k4_mcart_1(X6,X7,X8,X9) != sK5 | sK4 = X6) )),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f9,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3,X4,X5] : (k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X6] : (! [X7] : (! [X8] : (! [X9] : (X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5 | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0)) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.41/0.54    inference(flattening,[],[f8])).
% 1.41/0.54  fof(f8,plain,(
% 1.41/0.54    ? [X0,X1,X2,X3,X4,X5] : (((k8_mcart_1(X0,X1,X2,X3,X5) != X4 & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X6] : (! [X7] : (! [X8] : (! [X9] : ((X4 = X6 | k4_mcart_1(X6,X7,X8,X9) != X5) | ~m1_subset_1(X9,X3)) | ~m1_subset_1(X8,X2)) | ~m1_subset_1(X7,X1)) | ~m1_subset_1(X6,X0))) & m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.41/0.54    inference(ennf_transformation,[],[f7])).
% 1.41/0.54  fof(f7,negated_conjecture,(
% 1.41/0.54    ~! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.41/0.54    inference(negated_conjecture,[],[f6])).
% 1.41/0.54  fof(f6,conjecture,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(X5,k4_zfmisc_1(X0,X1,X2,X3)) => (! [X6] : (m1_subset_1(X6,X0) => ! [X7] : (m1_subset_1(X7,X1) => ! [X8] : (m1_subset_1(X8,X2) => ! [X9] : (m1_subset_1(X9,X3) => (k4_mcart_1(X6,X7,X8,X9) = X5 => X4 = X6))))) => (k8_mcart_1(X0,X1,X2,X3,X5) = X4 | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4)),sK8(X0,X1,X2,X3,X4)),sK9(X0,X1,X2,X3,X4)) = X4 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0) )),
% 1.41/0.54    inference(definition_unfolding,[],[f28,f36])).
% 1.41/0.54  fof(f28,plain,(
% 1.41/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k4_mcart_1(sK6(X0,X1,X2,X3,X4),sK7(X0,X1,X2,X3,X4),sK8(X0,X1,X2,X3,X4),sK9(X0,X1,X2,X3,X4)) = X4) )),
% 1.41/0.54    inference(cnf_transformation,[],[f11])).
% 1.41/0.54  fof(f19,plain,(
% 1.41/0.54    k1_xboole_0 != sK3),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f18,plain,(
% 1.41/0.54    k1_xboole_0 != sK2),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f17,plain,(
% 1.41/0.54    k1_xboole_0 != sK1),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f16,plain,(
% 1.41/0.54    k1_xboole_0 != sK0),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f46,plain,(
% 1.41/0.54    ( ! [X6,X2,X0,X8,X7,X5,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8)) = X5 | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | ~m1_subset_1(k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8),k4_zfmisc_1(X0,X1,X2,X3))) )),
% 1.41/0.54    inference(equality_resolution,[],[f42])).
% 1.41/0.54  fof(f42,plain,(
% 1.41/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_tarski(k4_tarski(k4_tarski(X5,X6),X7),X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.41/0.54    inference(definition_unfolding,[],[f32,f36])).
% 1.41/0.54  fof(f32,plain,(
% 1.41/0.54    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X2 | k1_xboole_0 = X3 | k4_mcart_1(X5,X6,X7,X8) != X4 | k8_mcart_1(X0,X1,X2,X3,X4) = X5) )),
% 1.41/0.54    inference(cnf_transformation,[],[f13])).
% 1.41/0.54  fof(f13,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : (! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.41/0.54    inference(flattening,[],[f12])).
% 1.41/0.54  fof(f12,plain,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : ((! [X5,X6,X7,X8] : ((k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) | k4_mcart_1(X5,X6,X7,X8) != X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)))),
% 1.41/0.54    inference(ennf_transformation,[],[f5])).
% 1.41/0.54  fof(f5,axiom,(
% 1.41/0.54    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => ~(? [X5,X6,X7,X8] : (~(k11_mcart_1(X0,X1,X2,X3,X4) = X8 & k10_mcart_1(X0,X1,X2,X3,X4) = X7 & k9_mcart_1(X0,X1,X2,X3,X4) = X6 & k8_mcart_1(X0,X1,X2,X3,X4) = X5) & k4_mcart_1(X5,X6,X7,X8) = X4) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0))),
% 1.41/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).
% 1.41/0.54  fof(f75,plain,(
% 1.41/0.54    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5) | spl10_6),
% 1.41/0.54    inference(avatar_component_clause,[],[f73])).
% 1.41/0.54  fof(f76,plain,(
% 1.41/0.54    ~spl10_6),
% 1.41/0.54    inference(avatar_split_clause,[],[f20,f73])).
% 1.41/0.54  fof(f20,plain,(
% 1.41/0.54    sK4 != k8_mcart_1(sK0,sK1,sK2,sK3,sK5)),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f71,plain,(
% 1.41/0.54    spl10_5),
% 1.41/0.54    inference(avatar_split_clause,[],[f15,f68])).
% 1.41/0.54  fof(f15,plain,(
% 1.41/0.54    m1_subset_1(sK5,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 1.41/0.54    inference(cnf_transformation,[],[f9])).
% 1.41/0.54  fof(f66,plain,(
% 1.41/0.54    ~spl10_4),
% 1.41/0.54    inference(avatar_split_clause,[],[f19,f63])).
% 1.41/0.54  fof(f61,plain,(
% 1.41/0.54    ~spl10_3),
% 1.41/0.54    inference(avatar_split_clause,[],[f18,f58])).
% 1.41/0.54  fof(f56,plain,(
% 1.41/0.54    ~spl10_2),
% 1.41/0.54    inference(avatar_split_clause,[],[f17,f53])).
% 1.41/0.54  fof(f51,plain,(
% 1.41/0.54    ~spl10_1),
% 1.41/0.54    inference(avatar_split_clause,[],[f16,f48])).
% 1.41/0.54  % SZS output end Proof for theBenchmark
% 1.41/0.54  % (672)------------------------------
% 1.41/0.54  % (672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (672)Termination reason: Refutation
% 1.41/0.54  
% 1.41/0.54  % (672)Memory used [KB]: 11129
% 1.41/0.54  % (672)Time elapsed: 0.077 s
% 1.41/0.54  % (672)------------------------------
% 1.41/0.54  % (672)------------------------------
% 1.41/0.54  % (632)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.54  % (675)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.55  % (642)Refutation not found, incomplete strategy% (642)------------------------------
% 1.41/0.55  % (642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (642)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (642)Memory used [KB]: 10746
% 1.41/0.55  % (642)Time elapsed: 0.133 s
% 1.41/0.55  % (642)------------------------------
% 1.41/0.55  % (642)------------------------------
% 1.41/0.55  % (670)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (663)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.55  % (623)Success in time 0.188 s
%------------------------------------------------------------------------------
