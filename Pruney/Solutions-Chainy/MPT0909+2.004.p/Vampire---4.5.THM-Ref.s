%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:23 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 641 expanded)
%              Number of leaves         :   26 ( 178 expanded)
%              Depth                    :   20
%              Number of atoms          :  512 (2617 expanded)
%              Number of equality atoms :  198 (1345 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1909,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f442,f1098,f1616,f1728,f1791,f1805,f1852,f1908])).

fof(f1908,plain,
    ( spl11_1
    | ~ spl11_7 ),
    inference(avatar_contradiction_clause,[],[f1907])).

fof(f1907,plain,
    ( $false
    | spl11_1
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f1905,f66])).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1905,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | spl11_1
    | ~ spl11_7 ),
    inference(resolution,[],[f1605,f142])).

fof(f142,plain,
    ( r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4))
    | spl11_1 ),
    inference(resolution,[],[f80,f139])).

fof(f139,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f136,f128])).

fof(f128,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl11_1
  <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f136,plain,
    ( r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(resolution,[],[f68,f104])).

fof(f104,plain,(
    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) ),
    inference(definition_unfolding,[],[f57,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f57,plain,(
    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK6 != k5_mcart_1(sK3,sK4,sK5,sK7)
    & k1_xboole_0 != sK5
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK6 = X5
                | k3_mcart_1(X5,X6,X7) != sK7
                | ~ m1_subset_1(X7,sK5) )
            | ~ m1_subset_1(X6,sK4) )
        | ~ m1_subset_1(X5,sK3) )
    & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k5_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X5
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK6 != k5_mcart_1(sK3,sK4,sK5,sK7)
      & k1_xboole_0 != sK5
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK6 = X5
                  | k3_mcart_1(X5,X6,X7) != sK7
                  | ~ m1_subset_1(X7,sK5) )
              | ~ m1_subset_1(X6,sK4) )
          | ~ m1_subset_1(X5,sK3) )
      & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k5_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X5
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

% (11248)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% (11244)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f1605,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f1604])).

fof(f1604,plain,
    ( spl11_7
  <=> ! [X0] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f1852,plain,
    ( spl11_6
    | spl11_7
    | spl11_1
    | spl11_4
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f1851,f1597,f439,f126,f1604,f1601])).

fof(f1601,plain,
    ( spl11_6
  <=> ! [X1] :
        ( ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f439,plain,
    ( spl11_4
  <=> sK6 = k1_mcart_1(k1_mcart_1(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f1597,plain,
    ( spl11_5
  <=> m1_subset_1(k2_mcart_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f1851,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | spl11_1
    | spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f1850,f143])).

fof(f143,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3)
    | spl11_1 ),
    inference(resolution,[],[f142,f80])).

fof(f1850,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) )
    | spl11_1
    | spl11_4
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f1849,f1598])).

fof(f1598,plain,
    ( m1_subset_1(k2_mcart_1(sK7),sK5)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f1597])).

fof(f1849,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) )
    | spl11_1
    | spl11_4 ),
    inference(subsumption_resolution,[],[f1848,f441])).

fof(f441,plain,
    ( sK6 != k1_mcart_1(k1_mcart_1(sK7))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f439])).

fof(f1848,plain,
    ( ! [X0,X1] :
        ( sK6 = k1_mcart_1(k1_mcart_1(sK7))
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) )
    | spl11_1 ),
    inference(trivial_inequality_removal,[],[f1846])).

fof(f1846,plain,
    ( ! [X0,X1] :
        ( sK7 != sK7
        | sK6 = k1_mcart_1(k1_mcart_1(sK7))
        | ~ r2_hidden(k1_mcart_1(sK7),X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1)
        | ~ m1_subset_1(k2_mcart_1(sK7),sK5)
        | ~ r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) )
    | spl11_1 ),
    inference(resolution,[],[f148,f1547])).

fof(f1547,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k2_mcart_1(k1_mcart_1(X3)),sK4)
      | sK7 != X3
      | k1_mcart_1(k1_mcart_1(X3)) = sK6
      | ~ r2_hidden(k1_mcart_1(X3),X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v1_relat_1(X5)
      | ~ m1_subset_1(k2_mcart_1(X3),sK5)
      | ~ r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK3) ) ),
    inference(resolution,[],[f1545,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f1545,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK3)
      | ~ m1_subset_1(k2_mcart_1(X3),sK5)
      | sK7 != X3
      | k1_mcart_1(k1_mcart_1(X3)) = sK6
      | ~ r2_hidden(k1_mcart_1(X3),X4)
      | ~ v1_relat_1(X4)
      | ~ r2_hidden(X3,X5)
      | ~ v1_relat_1(X5)
      | ~ r2_hidden(k2_mcart_1(k1_mcart_1(X3)),sK4) ) ),
    inference(resolution,[],[f256,f73])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK4)
      | sK6 = k1_mcart_1(k1_mcart_1(X0))
      | ~ m1_subset_1(k2_mcart_1(X0),sK5)
      | sK7 != X0
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK3)
      | ~ r2_hidden(k1_mcart_1(X0),X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f255,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f255,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X0,X1) != sK7
      | k1_mcart_1(X0) = sK6
      | ~ m1_subset_1(X1,sK5)
      | ~ m1_subset_1(k2_mcart_1(X0),sK4)
      | ~ m1_subset_1(k1_mcart_1(X0),sK3)
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f103,f72])).

fof(f103,plain,(
    ! [X6,X7,X5] :
      ( sK7 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK6 = X5
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(definition_unfolding,[],[f58,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f58,plain,(
    ! [X6,X7,X5] :
      ( sK6 = X5
      | k3_mcart_1(X5,X6,X7) != sK7
      | ~ m1_subset_1(X7,sK5)
      | ~ m1_subset_1(X6,sK4)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f148,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4)
    | spl11_1 ),
    inference(resolution,[],[f81,f142])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1805,plain,
    ( spl11_10
    | spl11_1 ),
    inference(avatar_split_clause,[],[f147,f126,f1627])).

fof(f1627,plain,
    ( spl11_10
  <=> r2_hidden(k2_mcart_1(sK7),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f147,plain,
    ( r2_hidden(k2_mcart_1(sK7),sK5)
    | spl11_1 ),
    inference(resolution,[],[f81,f139])).

fof(f1791,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f1790])).

fof(f1790,plain,
    ( $false
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1789,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f1789,plain,
    ( k1_xboole_0 = sK4
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1788,f59])).

fof(f59,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f36])).

fof(f1788,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1771,f122])).

fof(f122,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f121,f65])).

fof(f65,plain,(
    ! [X0] :
      ( r2_hidden(sK8(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK8(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
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

fof(f121,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f76,f63])).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1771,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK4
    | ~ spl11_1 ),
    inference(superposition,[],[f1189,f1724])).

fof(f1724,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f1708,f61])).

fof(f61,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f36])).

fof(f1708,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 = sK5
    | ~ spl11_1 ),
    inference(resolution,[],[f127,f1189])).

fof(f127,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f1189,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(condensation,[],[f1188])).

fof(f1188,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(subsumption_resolution,[],[f1162,f352])).

fof(f352,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k2_zfmisc_1(X7,X8)
      | ~ v1_xboole_0(X7) ) ),
    inference(superposition,[],[f313,f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f163,f273])).

fof(f273,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f264,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f264,plain,(
    ! [X2] :
      ( r2_hidden(sK9(X2,k1_xboole_0),X2)
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f74,f121])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK9(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1),X1)
          | ~ r2_hidden(sK9(X0,X1),X0) )
        & ( r2_hidden(sK9(X0,X1),X1)
          | r2_hidden(sK9(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f163,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f117,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f100,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f95,f78])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X3
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f117,plain,(
    ! [X0,X3,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f99,f102])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X2
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f313,plain,(
    ! [X15,X16] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X15,k1_xboole_0),X16) ),
    inference(subsumption_resolution,[],[f305,f231])).

fof(f231,plain,(
    ! [X2] : v1_xboole_0(k2_zfmisc_1(X2,k1_xboole_0)) ),
    inference(resolution,[],[f146,f121])).

fof(f146,plain,(
    ! [X0,X1] :
      ( r2_hidden(k2_mcart_1(sK8(k2_zfmisc_1(X0,X1))),X1)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(resolution,[],[f81,f65])).

fof(f305,plain,(
    ! [X15,X16] :
      ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X15,k1_xboole_0),X16)
      | ~ v1_xboole_0(k2_zfmisc_1(X15,k1_xboole_0)) ) ),
    inference(superposition,[],[f118,f286])).

fof(f286,plain,(
    ! [X0] :
      ( k2_zfmisc_1(X0,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f150,f273])).

fof(f150,plain,(
    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f116,f116])).

fof(f118,plain,(
    ! [X2,X0,X3] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ) ),
    inference(definition_unfolding,[],[f98,f102])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1162,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | ~ v1_xboole_0(k2_zfmisc_1(X1,X2)) ) ),
    inference(condensation,[],[f1118])).

fof(f1118,plain,(
    ! [X19,X17,X18,X16] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X19)
      | k1_xboole_0 = X19
      | k1_xboole_0 = X18
      | k1_xboole_0 = X17
      | k1_xboole_0 = X16
      | ~ v1_xboole_0(k2_zfmisc_1(X16,X17)) ) ),
    inference(superposition,[],[f112,f288])).

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f96,f102])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1728,plain,
    ( ~ spl11_10
    | spl11_5 ),
    inference(avatar_split_clause,[],[f1727,f1597,f1627])).

fof(f1727,plain,
    ( ~ r2_hidden(k2_mcart_1(sK7),sK5)
    | spl11_5 ),
    inference(resolution,[],[f1599,f73])).

fof(f1599,plain,
    ( ~ m1_subset_1(k2_mcart_1(sK7),sK5)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f1597])).

fof(f1616,plain,
    ( spl11_1
    | ~ spl11_6 ),
    inference(avatar_contradiction_clause,[],[f1615])).

fof(f1615,plain,
    ( $false
    | spl11_1
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f1613,f66])).

fof(f1613,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))
    | spl11_1
    | ~ spl11_6 ),
    inference(resolution,[],[f1602,f139])).

fof(f1602,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK7,X1)
        | ~ v1_relat_1(X1) )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f1601])).

fof(f1098,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f1097,f435])).

fof(f435,plain,
    ( spl11_3
  <=> sP2(sK7,sK5,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f1097,plain,(
    sP2(sK7,sK5,sK4,sK3) ),
    inference(subsumption_resolution,[],[f1096,f59])).

fof(f1096,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f1095,f60])).

fof(f1095,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f1058,f61])).

fof(f1058,plain,
    ( sP2(sK7,sK5,sK4,sK3)
    | k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f107,f104])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | sP2(X3,X2,X1,X0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f94,f78])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP2(X3,X2,X1,X0)
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f29,f33])).

fof(f33,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f442,plain,
    ( ~ spl11_3
    | ~ spl11_4 ),
    inference(avatar_split_clause,[],[f433,f439,f435])).

fof(f433,plain,
    ( sK6 != k1_mcart_1(k1_mcart_1(sK7))
    | ~ sP2(sK7,sK5,sK4,sK3) ),
    inference(superposition,[],[f62,f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0)
        & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0))
        & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X3,X2,X1,X0] :
      ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
        & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
        & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f62,plain,(
    sK6 != k5_mcart_1(sK3,sK4,sK5,sK7) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:32:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11196)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (11188)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (11180)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (11202)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (11174)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (11175)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (11176)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (11177)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (11178)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (11196)Refutation not found, incomplete strategy% (11196)------------------------------
% 0.22/0.53  % (11196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11196)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (11196)Memory used [KB]: 10874
% 0.22/0.53  % (11196)Time elapsed: 0.066 s
% 0.22/0.53  % (11196)------------------------------
% 0.22/0.53  % (11196)------------------------------
% 0.22/0.54  % (11189)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (11179)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (11191)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (11192)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (11193)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (11174)Refutation not found, incomplete strategy% (11174)------------------------------
% 0.22/0.54  % (11174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11174)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11174)Memory used [KB]: 1791
% 0.22/0.54  % (11174)Time elapsed: 0.125 s
% 0.22/0.54  % (11174)------------------------------
% 0.22/0.54  % (11174)------------------------------
% 0.22/0.54  % (11190)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (11186)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (11181)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (11182)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (11187)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (11194)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (11184)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (11194)Refutation not found, incomplete strategy% (11194)------------------------------
% 0.22/0.55  % (11194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11194)Memory used [KB]: 10746
% 0.22/0.55  % (11194)Time elapsed: 0.138 s
% 0.22/0.55  % (11194)------------------------------
% 0.22/0.55  % (11194)------------------------------
% 0.22/0.55  % (11198)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (11183)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (11184)Refutation not found, incomplete strategy% (11184)------------------------------
% 0.22/0.55  % (11184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11184)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11184)Memory used [KB]: 10618
% 0.22/0.55  % (11184)Time elapsed: 0.137 s
% 0.22/0.55  % (11184)------------------------------
% 0.22/0.55  % (11184)------------------------------
% 0.22/0.55  % (11185)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (11195)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (11176)Refutation not found, incomplete strategy% (11176)------------------------------
% 0.22/0.55  % (11176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11176)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11176)Memory used [KB]: 10746
% 0.22/0.55  % (11176)Time elapsed: 0.116 s
% 0.22/0.55  % (11176)------------------------------
% 0.22/0.55  % (11176)------------------------------
% 0.22/0.55  % (11199)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (11195)Refutation not found, incomplete strategy% (11195)------------------------------
% 0.22/0.55  % (11195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (11195)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (11195)Memory used [KB]: 1791
% 0.22/0.55  % (11195)Time elapsed: 0.134 s
% 0.22/0.55  % (11195)------------------------------
% 0.22/0.55  % (11195)------------------------------
% 1.48/0.56  % (11191)Refutation not found, incomplete strategy% (11191)------------------------------
% 1.48/0.56  % (11191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (11191)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (11191)Memory used [KB]: 10746
% 1.48/0.56  % (11191)Time elapsed: 0.137 s
% 1.48/0.56  % (11191)------------------------------
% 1.48/0.56  % (11191)------------------------------
% 1.48/0.56  % (11200)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.48/0.56  % (11203)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.48/0.56  % (11197)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.57  % (11201)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.12/0.65  % (11201)Refutation found. Thanks to Tanya!
% 2.12/0.65  % SZS status Theorem for theBenchmark
% 2.12/0.65  % SZS output start Proof for theBenchmark
% 2.12/0.65  fof(f1909,plain,(
% 2.12/0.65    $false),
% 2.12/0.65    inference(avatar_sat_refutation,[],[f442,f1098,f1616,f1728,f1791,f1805,f1852,f1908])).
% 2.12/0.65  fof(f1908,plain,(
% 2.12/0.65    spl11_1 | ~spl11_7),
% 2.12/0.65    inference(avatar_contradiction_clause,[],[f1907])).
% 2.12/0.65  fof(f1907,plain,(
% 2.12/0.65    $false | (spl11_1 | ~spl11_7)),
% 2.12/0.65    inference(subsumption_resolution,[],[f1905,f66])).
% 2.12/0.65  fof(f66,plain,(
% 2.12/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.12/0.65    inference(cnf_transformation,[],[f9])).
% 2.12/0.65  fof(f9,axiom,(
% 2.12/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.12/0.65  fof(f1905,plain,(
% 2.12/0.65    ~v1_relat_1(k2_zfmisc_1(sK3,sK4)) | (spl11_1 | ~spl11_7)),
% 2.12/0.65    inference(resolution,[],[f1605,f142])).
% 2.12/0.65  fof(f142,plain,(
% 2.12/0.65    r2_hidden(k1_mcart_1(sK7),k2_zfmisc_1(sK3,sK4)) | spl11_1),
% 2.12/0.65    inference(resolution,[],[f80,f139])).
% 2.12/0.65  fof(f139,plain,(
% 2.12/0.65    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl11_1),
% 2.12/0.65    inference(subsumption_resolution,[],[f136,f128])).
% 2.12/0.65  fof(f128,plain,(
% 2.12/0.65    ~v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | spl11_1),
% 2.12/0.65    inference(avatar_component_clause,[],[f126])).
% 2.12/0.65  fof(f126,plain,(
% 2.12/0.65    spl11_1 <=> v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.12/0.65    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 2.12/0.65  fof(f136,plain,(
% 2.12/0.65    r2_hidden(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.12/0.65    inference(resolution,[],[f68,f104])).
% 2.12/0.65  fof(f104,plain,(
% 2.12/0.65    m1_subset_1(sK7,k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5))),
% 2.12/0.65    inference(definition_unfolding,[],[f57,f78])).
% 2.12/0.65  fof(f78,plain,(
% 2.12/0.65    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.12/0.65    inference(cnf_transformation,[],[f12])).
% 2.12/0.65  fof(f12,axiom,(
% 2.12/0.65    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.12/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.12/0.65  fof(f57,plain,(
% 2.12/0.65    m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.12/0.65    inference(cnf_transformation,[],[f36])).
% 2.12/0.65  fof(f36,plain,(
% 2.12/0.65    sK6 != k5_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5))),
% 2.12/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f21,f35])).
% 2.12/0.65  fof(f35,plain,(
% 2.12/0.65    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK6 != k5_mcart_1(sK3,sK4,sK5,sK7) & k1_xboole_0 != sK5 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & ! [X5] : (! [X6] : (! [X7] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5)) | ~m1_subset_1(X6,sK4)) | ~m1_subset_1(X5,sK3)) & m1_subset_1(sK7,k3_zfmisc_1(sK3,sK4,sK5)))),
% 2.12/0.65    introduced(choice_axiom,[])).
% 2.12/0.65  fof(f21,plain,(
% 2.12/0.65    ? [X0,X1,X2,X3,X4] : (k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X5 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.12/0.65    inference(flattening,[],[f20])).
% 2.12/0.65  fof(f20,plain,(
% 2.12/0.65    ? [X0,X1,X2,X3,X4] : (((k5_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X5 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 2.12/0.65    inference(ennf_transformation,[],[f19])).
% 2.12/0.65  % (11248)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.12/0.66  % (11244)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.12/0.66  fof(f19,negated_conjecture,(
% 2.12/0.66    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.12/0.66    inference(negated_conjecture,[],[f18])).
% 2.12/0.66  fof(f18,conjecture,(
% 2.12/0.66    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X5)))) => (k5_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).
% 2.12/0.66  fof(f68,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f41])).
% 2.12/0.66  fof(f41,plain,(
% 2.12/0.66    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.12/0.66    inference(nnf_transformation,[],[f22])).
% 2.12/0.66  fof(f22,plain,(
% 2.12/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.12/0.66    inference(ennf_transformation,[],[f7])).
% 2.12/0.66  fof(f7,axiom,(
% 2.12/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.12/0.66  fof(f80,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f28])).
% 2.12/0.66  fof(f28,plain,(
% 2.12/0.66    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 2.12/0.66    inference(ennf_transformation,[],[f14])).
% 2.12/0.66  fof(f14,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 2.12/0.66  fof(f1605,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0)) ) | ~spl11_7),
% 2.12/0.66    inference(avatar_component_clause,[],[f1604])).
% 2.12/0.66  fof(f1604,plain,(
% 2.12/0.66    spl11_7 <=> ! [X0] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 2.12/0.66  fof(f1852,plain,(
% 2.12/0.66    spl11_6 | spl11_7 | spl11_1 | spl11_4 | ~spl11_5),
% 2.12/0.66    inference(avatar_split_clause,[],[f1851,f1597,f439,f126,f1604,f1601])).
% 2.12/0.66  fof(f1601,plain,(
% 2.12/0.66    spl11_6 <=> ! [X1] : (~r2_hidden(sK7,X1) | ~v1_relat_1(X1))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 2.12/0.66  fof(f439,plain,(
% 2.12/0.66    spl11_4 <=> sK6 = k1_mcart_1(k1_mcart_1(sK7))),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 2.12/0.66  fof(f1597,plain,(
% 2.12/0.66    spl11_5 <=> m1_subset_1(k2_mcart_1(sK7),sK5)),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 2.12/0.66  fof(f1851,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | (spl11_1 | spl11_4 | ~spl11_5)),
% 2.12/0.66    inference(subsumption_resolution,[],[f1850,f143])).
% 2.12/0.66  fof(f143,plain,(
% 2.12/0.66    r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3) | spl11_1),
% 2.12/0.66    inference(resolution,[],[f142,f80])).
% 2.12/0.66  fof(f1850,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3)) ) | (spl11_1 | spl11_4 | ~spl11_5)),
% 2.12/0.66    inference(subsumption_resolution,[],[f1849,f1598])).
% 2.12/0.66  fof(f1598,plain,(
% 2.12/0.66    m1_subset_1(k2_mcart_1(sK7),sK5) | ~spl11_5),
% 2.12/0.66    inference(avatar_component_clause,[],[f1597])).
% 2.12/0.66  fof(f1849,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3)) ) | (spl11_1 | spl11_4)),
% 2.12/0.66    inference(subsumption_resolution,[],[f1848,f441])).
% 2.12/0.66  fof(f441,plain,(
% 2.12/0.66    sK6 != k1_mcart_1(k1_mcart_1(sK7)) | spl11_4),
% 2.12/0.66    inference(avatar_component_clause,[],[f439])).
% 2.12/0.66  fof(f1848,plain,(
% 2.12/0.66    ( ! [X0,X1] : (sK6 = k1_mcart_1(k1_mcart_1(sK7)) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3)) ) | spl11_1),
% 2.12/0.66    inference(trivial_inequality_removal,[],[f1846])).
% 2.12/0.66  fof(f1846,plain,(
% 2.12/0.66    ( ! [X0,X1] : (sK7 != sK7 | sK6 = k1_mcart_1(k1_mcart_1(sK7)) | ~r2_hidden(k1_mcart_1(sK7),X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7,X1) | ~v1_relat_1(X1) | ~m1_subset_1(k2_mcart_1(sK7),sK5) | ~r2_hidden(k1_mcart_1(k1_mcart_1(sK7)),sK3)) ) | spl11_1),
% 2.12/0.66    inference(resolution,[],[f148,f1547])).
% 2.12/0.66  fof(f1547,plain,(
% 2.12/0.66    ( ! [X4,X5,X3] : (~r2_hidden(k2_mcart_1(k1_mcart_1(X3)),sK4) | sK7 != X3 | k1_mcart_1(k1_mcart_1(X3)) = sK6 | ~r2_hidden(k1_mcart_1(X3),X4) | ~v1_relat_1(X4) | ~r2_hidden(X3,X5) | ~v1_relat_1(X5) | ~m1_subset_1(k2_mcart_1(X3),sK5) | ~r2_hidden(k1_mcart_1(k1_mcart_1(X3)),sK3)) )),
% 2.12/0.66    inference(resolution,[],[f1545,f73])).
% 2.12/0.66  fof(f73,plain,(
% 2.12/0.66    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f25])).
% 2.12/0.66  fof(f25,plain,(
% 2.12/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f8])).
% 2.12/0.66  fof(f8,axiom,(
% 2.12/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.12/0.66  fof(f1545,plain,(
% 2.12/0.66    ( ! [X4,X5,X3] : (~m1_subset_1(k1_mcart_1(k1_mcart_1(X3)),sK3) | ~m1_subset_1(k2_mcart_1(X3),sK5) | sK7 != X3 | k1_mcart_1(k1_mcart_1(X3)) = sK6 | ~r2_hidden(k1_mcart_1(X3),X4) | ~v1_relat_1(X4) | ~r2_hidden(X3,X5) | ~v1_relat_1(X5) | ~r2_hidden(k2_mcart_1(k1_mcart_1(X3)),sK4)) )),
% 2.12/0.66    inference(resolution,[],[f256,f73])).
% 2.12/0.66  fof(f256,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(k2_mcart_1(k1_mcart_1(X0)),sK4) | sK6 = k1_mcart_1(k1_mcart_1(X0)) | ~m1_subset_1(k2_mcart_1(X0),sK5) | sK7 != X0 | ~m1_subset_1(k1_mcart_1(k1_mcart_1(X0)),sK3) | ~r2_hidden(k1_mcart_1(X0),X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 2.12/0.66    inference(superposition,[],[f255,f72])).
% 2.12/0.66  fof(f72,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f24])).
% 2.12/0.66  fof(f24,plain,(
% 2.12/0.66    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 2.12/0.66    inference(flattening,[],[f23])).
% 2.12/0.66  fof(f23,plain,(
% 2.12/0.66    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f15])).
% 2.12/0.66  fof(f15,axiom,(
% 2.12/0.66    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 2.12/0.66  fof(f255,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k4_tarski(X0,X1) != sK7 | k1_mcart_1(X0) = sK6 | ~m1_subset_1(X1,sK5) | ~m1_subset_1(k2_mcart_1(X0),sK4) | ~m1_subset_1(k1_mcart_1(X0),sK3) | ~r2_hidden(X0,X2) | ~v1_relat_1(X2)) )),
% 2.12/0.66    inference(superposition,[],[f103,f72])).
% 2.12/0.66  fof(f103,plain,(
% 2.12/0.66    ( ! [X6,X7,X5] : (sK7 != k4_tarski(k4_tarski(X5,X6),X7) | sK6 = X5 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f58,f77])).
% 2.12/0.66  fof(f77,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f11])).
% 2.12/0.66  fof(f11,axiom,(
% 2.12/0.66    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.12/0.66  fof(f58,plain,(
% 2.12/0.66    ( ! [X6,X7,X5] : (sK6 = X5 | k3_mcart_1(X5,X6,X7) != sK7 | ~m1_subset_1(X7,sK5) | ~m1_subset_1(X6,sK4) | ~m1_subset_1(X5,sK3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f36])).
% 2.12/0.66  fof(f148,plain,(
% 2.12/0.66    r2_hidden(k2_mcart_1(k1_mcart_1(sK7)),sK4) | spl11_1),
% 2.12/0.66    inference(resolution,[],[f81,f142])).
% 2.12/0.66  fof(f81,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f28])).
% 2.12/0.66  fof(f1805,plain,(
% 2.12/0.66    spl11_10 | spl11_1),
% 2.12/0.66    inference(avatar_split_clause,[],[f147,f126,f1627])).
% 2.12/0.66  fof(f1627,plain,(
% 2.12/0.66    spl11_10 <=> r2_hidden(k2_mcart_1(sK7),sK5)),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).
% 2.12/0.66  fof(f147,plain,(
% 2.12/0.66    r2_hidden(k2_mcart_1(sK7),sK5) | spl11_1),
% 2.12/0.66    inference(resolution,[],[f81,f139])).
% 2.12/0.66  fof(f1791,plain,(
% 2.12/0.66    ~spl11_1),
% 2.12/0.66    inference(avatar_contradiction_clause,[],[f1790])).
% 2.12/0.66  fof(f1790,plain,(
% 2.12/0.66    $false | ~spl11_1),
% 2.12/0.66    inference(subsumption_resolution,[],[f1789,f60])).
% 2.12/0.66  fof(f60,plain,(
% 2.12/0.66    k1_xboole_0 != sK4),
% 2.12/0.66    inference(cnf_transformation,[],[f36])).
% 2.12/0.66  fof(f1789,plain,(
% 2.12/0.66    k1_xboole_0 = sK4 | ~spl11_1),
% 2.12/0.66    inference(subsumption_resolution,[],[f1788,f59])).
% 2.12/0.66  fof(f59,plain,(
% 2.12/0.66    k1_xboole_0 != sK3),
% 2.12/0.66    inference(cnf_transformation,[],[f36])).
% 2.12/0.66  fof(f1788,plain,(
% 2.12/0.66    k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl11_1),
% 2.12/0.66    inference(subsumption_resolution,[],[f1771,f122])).
% 2.12/0.66  fof(f122,plain,(
% 2.12/0.66    v1_xboole_0(k1_xboole_0)),
% 2.12/0.66    inference(resolution,[],[f121,f65])).
% 2.12/0.66  fof(f65,plain,(
% 2.12/0.66    ( ! [X0] : (r2_hidden(sK8(X0),X0) | v1_xboole_0(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f40])).
% 2.12/0.66  fof(f40,plain,(
% 2.12/0.66    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK8(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f38,f39])).
% 2.12/0.66  fof(f39,plain,(
% 2.12/0.66    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK8(X0),X0))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f38,plain,(
% 2.12/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.12/0.66    inference(rectify,[],[f37])).
% 2.12/0.66  fof(f37,plain,(
% 2.12/0.66    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.12/0.66    inference(nnf_transformation,[],[f1])).
% 2.12/0.66  fof(f1,axiom,(
% 2.12/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.12/0.66  fof(f121,plain,(
% 2.12/0.66    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.12/0.66    inference(resolution,[],[f76,f63])).
% 2.12/0.66  fof(f63,plain,(
% 2.12/0.66    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f3])).
% 2.12/0.66  fof(f3,axiom,(
% 2.12/0.66    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.12/0.66  fof(f76,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f27])).
% 2.12/0.66  fof(f27,plain,(
% 2.12/0.66    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.12/0.66    inference(ennf_transformation,[],[f10])).
% 2.12/0.66  fof(f10,axiom,(
% 2.12/0.66    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 2.12/0.66  fof(f1771,plain,(
% 2.12/0.66    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = sK3 | k1_xboole_0 = sK4 | ~spl11_1),
% 2.12/0.66    inference(superposition,[],[f1189,f1724])).
% 2.12/0.66  fof(f1724,plain,(
% 2.12/0.66    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | ~spl11_1),
% 2.12/0.66    inference(subsumption_resolution,[],[f1708,f61])).
% 2.12/0.66  fof(f61,plain,(
% 2.12/0.66    k1_xboole_0 != sK5),
% 2.12/0.66    inference(cnf_transformation,[],[f36])).
% 2.12/0.66  fof(f1708,plain,(
% 2.12/0.66    k1_xboole_0 = k2_zfmisc_1(sK3,sK4) | k1_xboole_0 = sK5 | ~spl11_1),
% 2.12/0.66    inference(resolution,[],[f127,f1189])).
% 2.12/0.66  fof(f127,plain,(
% 2.12/0.66    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | ~spl11_1),
% 2.12/0.66    inference(avatar_component_clause,[],[f126])).
% 2.12/0.66  fof(f1189,plain,(
% 2.12/0.66    ( ! [X0,X1] : (~v1_xboole_0(k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.12/0.66    inference(condensation,[],[f1188])).
% 2.12/0.66  fof(f1188,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f1162,f352])).
% 2.12/0.66  fof(f352,plain,(
% 2.12/0.66    ( ! [X8,X7] : (k1_xboole_0 = k2_zfmisc_1(X7,X8) | ~v1_xboole_0(X7)) )),
% 2.12/0.66    inference(superposition,[],[f313,f288])).
% 2.12/0.66  fof(f288,plain,(
% 2.12/0.66    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 2.12/0.66    inference(superposition,[],[f163,f273])).
% 2.12/0.66  fof(f273,plain,(
% 2.12/0.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.12/0.66    inference(resolution,[],[f264,f64])).
% 2.12/0.66  fof(f64,plain,(
% 2.12/0.66    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f40])).
% 2.12/0.66  fof(f264,plain,(
% 2.12/0.66    ( ! [X2] : (r2_hidden(sK9(X2,k1_xboole_0),X2) | k1_xboole_0 = X2) )),
% 2.12/0.66    inference(resolution,[],[f74,f121])).
% 2.12/0.66  fof(f74,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | X0 = X1 | r2_hidden(sK9(X0,X1),X0)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f44])).
% 2.12/0.66  fof(f44,plain,(
% 2.12/0.66    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 2.12/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f42,f43])).
% 2.12/0.66  fof(f43,plain,(
% 2.12/0.66    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK9(X0,X1),X1) | ~r2_hidden(sK9(X0,X1),X0)) & (r2_hidden(sK9(X0,X1),X1) | r2_hidden(sK9(X0,X1),X0))))),
% 2.12/0.66    introduced(choice_axiom,[])).
% 2.12/0.66  fof(f42,plain,(
% 2.12/0.66    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.12/0.66    inference(nnf_transformation,[],[f26])).
% 2.12/0.66  fof(f26,plain,(
% 2.12/0.66    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.12/0.66    inference(ennf_transformation,[],[f2])).
% 2.12/0.66  fof(f2,axiom,(
% 2.12/0.66    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 2.12/0.66  fof(f163,plain,(
% 2.12/0.66    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 2.12/0.66    inference(superposition,[],[f117,f116])).
% 2.12/0.66  fof(f116,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),k1_xboole_0)) )),
% 2.12/0.66    inference(equality_resolution,[],[f108])).
% 2.12/0.66  fof(f108,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f100,f102])).
% 2.12/0.66  fof(f102,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f95,f78])).
% 2.12/0.66  fof(f95,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f13])).
% 2.12/0.66  fof(f13,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 2.12/0.66  fof(f100,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X3 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f56])).
% 2.12/0.66  fof(f56,plain,(
% 2.12/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.12/0.66    inference(flattening,[],[f55])).
% 2.12/0.66  fof(f55,plain,(
% 2.12/0.66    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 2.12/0.66    inference(nnf_transformation,[],[f17])).
% 2.12/0.66  fof(f17,axiom,(
% 2.12/0.66    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 2.12/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 2.12/0.66  fof(f117,plain,(
% 2.12/0.66    ( ! [X0,X3,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k1_xboole_0),X3)) )),
% 2.12/0.66    inference(equality_resolution,[],[f109])).
% 2.12/0.66  fof(f109,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f99,f102])).
% 2.12/0.66  fof(f99,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X2 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f56])).
% 2.12/0.66  fof(f313,plain,(
% 2.12/0.66    ( ! [X15,X16] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X15,k1_xboole_0),X16)) )),
% 2.12/0.66    inference(subsumption_resolution,[],[f305,f231])).
% 2.12/0.66  fof(f231,plain,(
% 2.12/0.66    ( ! [X2] : (v1_xboole_0(k2_zfmisc_1(X2,k1_xboole_0))) )),
% 2.12/0.66    inference(resolution,[],[f146,f121])).
% 2.12/0.66  fof(f146,plain,(
% 2.12/0.66    ( ! [X0,X1] : (r2_hidden(k2_mcart_1(sK8(k2_zfmisc_1(X0,X1))),X1) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 2.12/0.66    inference(resolution,[],[f81,f65])).
% 2.12/0.66  fof(f305,plain,(
% 2.12/0.66    ( ! [X15,X16] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X15,k1_xboole_0),X16) | ~v1_xboole_0(k2_zfmisc_1(X15,k1_xboole_0))) )),
% 2.12/0.66    inference(superposition,[],[f118,f286])).
% 2.12/0.66  fof(f286,plain,(
% 2.12/0.66    ( ! [X0] : (k2_zfmisc_1(X0,X0) = X0 | ~v1_xboole_0(X0)) )),
% 2.12/0.66    inference(superposition,[],[f150,f273])).
% 2.12/0.66  fof(f150,plain,(
% 2.12/0.66    k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,k1_xboole_0)),
% 2.12/0.66    inference(superposition,[],[f116,f116])).
% 2.12/0.66  fof(f118,plain,(
% 2.12/0.66    ( ! [X2,X0,X3] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0),X2),X3)) )),
% 2.12/0.66    inference(equality_resolution,[],[f110])).
% 2.12/0.66  fof(f110,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 2.12/0.66    inference(definition_unfolding,[],[f98,f102])).
% 2.12/0.66  fof(f98,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 2.12/0.66    inference(cnf_transformation,[],[f56])).
% 2.12/0.66  fof(f1162,plain,(
% 2.12/0.66    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X1,X2),X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | ~v1_xboole_0(k2_zfmisc_1(X1,X2))) )),
% 2.12/0.66    inference(condensation,[],[f1118])).
% 2.12/0.66  fof(f1118,plain,(
% 2.12/0.66    ( ! [X19,X17,X18,X16] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X16,X17),X19) | k1_xboole_0 = X19 | k1_xboole_0 = X18 | k1_xboole_0 = X17 | k1_xboole_0 = X16 | ~v1_xboole_0(k2_zfmisc_1(X16,X17))) )),
% 2.12/0.66    inference(superposition,[],[f112,f288])).
% 2.12/0.66  fof(f112,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.12/0.66    inference(definition_unfolding,[],[f96,f102])).
% 2.12/0.66  fof(f96,plain,(
% 2.12/0.66    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.12/0.66    inference(cnf_transformation,[],[f56])).
% 2.12/0.66  fof(f1728,plain,(
% 2.12/0.66    ~spl11_10 | spl11_5),
% 2.12/0.66    inference(avatar_split_clause,[],[f1727,f1597,f1627])).
% 2.12/0.66  fof(f1727,plain,(
% 2.12/0.66    ~r2_hidden(k2_mcart_1(sK7),sK5) | spl11_5),
% 2.12/0.66    inference(resolution,[],[f1599,f73])).
% 2.12/0.66  fof(f1599,plain,(
% 2.12/0.66    ~m1_subset_1(k2_mcart_1(sK7),sK5) | spl11_5),
% 2.12/0.66    inference(avatar_component_clause,[],[f1597])).
% 2.12/0.66  fof(f1616,plain,(
% 2.12/0.66    spl11_1 | ~spl11_6),
% 2.12/0.66    inference(avatar_contradiction_clause,[],[f1615])).
% 2.12/0.66  fof(f1615,plain,(
% 2.12/0.66    $false | (spl11_1 | ~spl11_6)),
% 2.12/0.66    inference(subsumption_resolution,[],[f1613,f66])).
% 2.12/0.66  fof(f1613,plain,(
% 2.12/0.66    ~v1_relat_1(k2_zfmisc_1(k2_zfmisc_1(sK3,sK4),sK5)) | (spl11_1 | ~spl11_6)),
% 2.12/0.66    inference(resolution,[],[f1602,f139])).
% 2.12/0.66  fof(f1602,plain,(
% 2.12/0.66    ( ! [X1] : (~r2_hidden(sK7,X1) | ~v1_relat_1(X1)) ) | ~spl11_6),
% 2.12/0.66    inference(avatar_component_clause,[],[f1601])).
% 2.12/0.66  fof(f1098,plain,(
% 2.12/0.66    spl11_3),
% 2.12/0.66    inference(avatar_split_clause,[],[f1097,f435])).
% 2.12/0.66  fof(f435,plain,(
% 2.12/0.66    spl11_3 <=> sP2(sK7,sK5,sK4,sK3)),
% 2.12/0.66    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 2.12/0.66  fof(f1097,plain,(
% 2.12/0.66    sP2(sK7,sK5,sK4,sK3)),
% 2.12/0.66    inference(subsumption_resolution,[],[f1096,f59])).
% 2.12/0.66  fof(f1096,plain,(
% 2.12/0.66    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK3),
% 2.12/0.66    inference(subsumption_resolution,[],[f1095,f60])).
% 2.12/0.66  fof(f1095,plain,(
% 2.12/0.66    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.12/0.66    inference(subsumption_resolution,[],[f1058,f61])).
% 2.12/0.67  fof(f1058,plain,(
% 2.12/0.67    sP2(sK7,sK5,sK4,sK3) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3),
% 2.12/0.67    inference(resolution,[],[f107,f104])).
% 2.12/0.67  fof(f107,plain,(
% 2.12/0.67    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | sP2(X3,X2,X1,X0) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.12/0.67    inference(definition_unfolding,[],[f94,f78])).
% 2.12/0.67  fof(f94,plain,(
% 2.12/0.67    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.12/0.67    inference(cnf_transformation,[],[f34])).
% 2.12/0.67  fof(f34,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (! [X3] : (sP2(X3,X2,X1,X0) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.12/0.67    inference(definition_folding,[],[f29,f33])).
% 2.12/0.67  fof(f33,plain,(
% 2.12/0.67    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.12/0.67    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.12/0.67  fof(f29,plain,(
% 2.12/0.67    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.12/0.67    inference(ennf_transformation,[],[f16])).
% 2.12/0.67  fof(f16,axiom,(
% 2.12/0.67    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.12/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 2.12/0.67  fof(f442,plain,(
% 2.12/0.67    ~spl11_3 | ~spl11_4),
% 2.12/0.67    inference(avatar_split_clause,[],[f433,f439,f435])).
% 2.12/0.67  fof(f433,plain,(
% 2.12/0.67    sK6 != k1_mcart_1(k1_mcart_1(sK7)) | ~sP2(sK7,sK5,sK4,sK3)),
% 2.12/0.67    inference(superposition,[],[f62,f91])).
% 2.12/0.67  fof(f91,plain,(
% 2.12/0.67    ( ! [X2,X0,X3,X1] : (k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0)) | ~sP2(X0,X1,X2,X3)) )),
% 2.12/0.67    inference(cnf_transformation,[],[f54])).
% 2.12/0.67  fof(f54,plain,(
% 2.12/0.67    ! [X0,X1,X2,X3] : ((k2_mcart_1(X0) = k7_mcart_1(X3,X2,X1,X0) & k6_mcart_1(X3,X2,X1,X0) = k2_mcart_1(k1_mcart_1(X0)) & k5_mcart_1(X3,X2,X1,X0) = k1_mcart_1(k1_mcart_1(X0))) | ~sP2(X0,X1,X2,X3))),
% 2.12/0.67    inference(rectify,[],[f53])).
% 2.12/0.67  fof(f53,plain,(
% 2.12/0.67    ! [X3,X2,X1,X0] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~sP2(X3,X2,X1,X0))),
% 2.12/0.67    inference(nnf_transformation,[],[f33])).
% 2.12/0.67  fof(f62,plain,(
% 2.12/0.67    sK6 != k5_mcart_1(sK3,sK4,sK5,sK7)),
% 2.12/0.67    inference(cnf_transformation,[],[f36])).
% 2.12/0.67  % SZS output end Proof for theBenchmark
% 2.12/0.67  % (11201)------------------------------
% 2.12/0.67  % (11201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.67  % (11201)Termination reason: Refutation
% 2.12/0.67  
% 2.12/0.67  % (11201)Memory used [KB]: 6908
% 2.12/0.67  % (11201)Time elapsed: 0.244 s
% 2.12/0.67  % (11201)------------------------------
% 2.12/0.67  % (11201)------------------------------
% 2.12/0.67  % (11173)Success in time 0.296 s
%------------------------------------------------------------------------------
