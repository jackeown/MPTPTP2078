%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  134 (2768 expanded)
%              Number of leaves         :   22 ( 737 expanded)
%              Depth                    :   29
%              Number of atoms          :  482 (13305 expanded)
%              Number of equality atoms :  112 (2188 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f537,plain,(
    $false ),
    inference(subsumption_resolution,[],[f501,f536])).

fof(f536,plain,(
    ! [X0] : v1_funct_2(sK4,k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f535,f526])).

fof(f526,plain,(
    ! [X2,X3] : sP2(X2,sK4,X3) ),
    inference(resolution,[],[f477,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

% (19375)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f477,plain,(
    ! [X0,X1] : m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ),
    inference(subsumption_resolution,[],[f440,f476])).

fof(f476,plain,(
    ! [X0] : r1_tarski(k1_relat_1(sK4),X0) ),
    inference(subsumption_resolution,[],[f471,f173])).

fof(f173,plain,(
    ! [X5] : ~ r2_hidden(X5,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f171,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,sK7(k1_xboole_0,X5)) ) ),
    inference(resolution,[],[f167,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f167,plain,(
    ! [X1] :
      ( r2_hidden(sK7(k1_xboole_0,X1),k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f166,f57])).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f166,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | r2_hidden(sK7(k1_xboole_0,X1),k1_relat_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f164,f62])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != sK5(X0,X1)
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
              & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( k1_funct_1(X0,X6) != X5
                  | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK7(X0,X5)) = X5
                & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).

fof(f34,plain,(
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
              ( k1_funct_1(X0,X3) != sK5(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK5(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK5(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1))
        & r2_hidden(sK6(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X5)) = X5
        & r2_hidden(sK7(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f164,plain,(
    sP0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f159,f59])).

fof(f159,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK5(k1_xboole_0,X2))
      | sP0(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f157,f79])).

fof(f157,plain,(
    ! [X5] :
      ( r2_hidden(sK5(k1_xboole_0,X5),X5)
      | sP0(k1_xboole_0,X5) ) ),
    inference(subsumption_resolution,[],[f149,f59])).

fof(f149,plain,(
    ! [X5] :
      ( r2_hidden(sK5(k1_xboole_0,X5),X5)
      | sP0(k1_xboole_0,X5)
      | ~ r1_tarski(k1_xboole_0,sK6(k1_xboole_0,X5)) ) ),
    inference(resolution,[],[f145,f79])).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(sK6(k1_xboole_0,X0),k1_xboole_0)
      | r2_hidden(sK5(k1_xboole_0,X0),X0)
      | sP0(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f65,f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK5(X0,X1),X1)
      | sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f471,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK4,sK8(k1_relat_1(sK4),X0)),k1_xboole_0)
      | r1_tarski(k1_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f439,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X2)
      | r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1)),X2)
      | r1_tarski(k1_relat_1(X0),X1) ) ),
    inference(resolution,[],[f90,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k1_relat_1(X0))
      | r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ sP0(X0,X1) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f439,plain,(
    sP0(sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f417,f173])).

fof(f417,plain,
    ( r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k1_xboole_0)
    | sP0(sK4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f244,f401])).

fof(f401,plain,(
    k1_xboole_0 = k2_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f400,f59])).

fof(f400,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK4))
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(forward_demodulation,[],[f379,f376])).

fof(f376,plain,(
    k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f375,f55])).

fof(f55,plain,(
    r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
      | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
      | ~ v1_funct_1(sK4) )
    & r1_tarski(k2_relat_1(sK4),sK3)
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
          | ~ v1_funct_1(X1) )
        & r1_tarski(k2_relat_1(X1),X0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
        | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
        | ~ v1_funct_1(sK4) )
      & r1_tarski(k2_relat_1(sK4),sK3)
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        | ~ v1_funct_2(X1,k1_relat_1(X1),X0)
        | ~ v1_funct_1(X1) )
      & r1_tarski(k2_relat_1(X1),X0)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(k2_relat_1(X1),X0)
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
            & v1_funct_2(X1,k1_relat_1(X1),X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f375,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relat_1(sK4),sK3) ),
    inference(resolution,[],[f374,f260])).

fof(f260,plain,(
    ! [X0] :
      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f259,f91])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f259,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X1)
      | ~ r1_tarski(k2_relat_1(sK4),X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

% (19375)Refutation not found, incomplete strategy% (19375)------------------------------
% (19375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19375)Termination reason: Refutation not found, incomplete strategy

% (19375)Memory used [KB]: 10746
% (19375)Time elapsed: 0.152 s
% (19375)------------------------------
% (19375)------------------------------
% (19384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (19369)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f374,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f372,f55])).

fof(f372,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(resolution,[],[f371,f100])).

fof(f100,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) ),
    inference(subsumption_resolution,[],[f56,f54])).

fof(f54,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3)
    | ~ v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f371,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,k1_relat_1(sK4),X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(subsumption_resolution,[],[f370,f261])).

fof(f261,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK4),X0)
      | k1_relat_1(sK4) = k1_relset_1(k1_relat_1(sK4),X0,sK4) ) ),
    inference(resolution,[],[f260,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f370,plain,(
    ! [X0] :
      ( k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),X0,sK4)
      | k1_xboole_0 = X0
      | v1_funct_2(sK4,k1_relat_1(sK4),X0)
      | ~ r1_tarski(k2_relat_1(sK4),X0) ) ),
    inference(resolution,[],[f84,f262])).

fof(f262,plain,(
    ! [X1] :
      ( sP2(k1_relat_1(sK4),sK4,X1)
      | ~ r1_tarski(k2_relat_1(sK4),X1) ) ),
    inference(resolution,[],[f260,f86])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 = X2
      | v1_funct_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f379,plain,
    ( k1_xboole_0 = k2_relat_1(sK4)
    | ~ r1_tarski(sK3,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f110,f376])).

fof(f110,plain,
    ( ~ r1_tarski(sK3,k2_relat_1(sK4))
    | sK3 = k2_relat_1(sK4) ),
    inference(resolution,[],[f71,f55])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f244,plain,
    ( r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k2_relat_1(sK4))
    | sP0(sK4,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f243,f53])).

fof(f243,plain,
    ( sP0(sK4,k1_xboole_0)
    | r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k2_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f210,f54])).

fof(f210,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP0(X0,k1_xboole_0)
      | r2_hidden(k1_funct_1(X0,sK6(X0,k1_xboole_0)),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f188,f101])).

fof(f101,plain,(
    ! [X0] :
      ( sP0(X0,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f89,f68])).

fof(f68,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f16,f25,f24])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | sP0(X0,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(k1_funct_1(X0,sK6(X0,k1_xboole_0)),X1)
      | sP0(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f175,f90])).

fof(f175,plain,(
    ! [X7] :
      ( r2_hidden(sK6(X7,k1_xboole_0),k1_relat_1(X7))
      | sP0(X7,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f142,f173])).

fof(f142,plain,(
    ! [X7] :
      ( r2_hidden(sK6(X7,k1_xboole_0),k1_relat_1(X7))
      | sP0(X7,k1_xboole_0)
      | r2_hidden(k4_tarski(sK11(k1_xboole_0,sK5(X7,k1_xboole_0)),sK5(X7,k1_xboole_0)),k1_xboole_0) ) ),
    inference(resolution,[],[f65,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r2_hidden(k4_tarski(sK11(k1_xboole_0,X0),X0),k1_xboole_0) ) ),
    inference(superposition,[],[f94,f58])).

fof(f58,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f94,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k2_relat_1(X0))
      | r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0)
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f45,f48,f47,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0)
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0)
     => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
     => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X4,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X7,X5),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X3,X2),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k2_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f440,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK4),X1)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(subsumption_resolution,[],[f420,f59])).

fof(f420,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | ~ r1_tarski(k1_relat_1(sK4),X1)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(backward_demodulation,[],[f259,f401])).

fof(f535,plain,(
    ! [X0] :
      ( v1_funct_2(sK4,k1_xboole_0,X0)
      | ~ sP2(k1_xboole_0,sK4,X0) ) ),
    inference(trivial_inequality_removal,[],[f534])).

fof(f534,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | v1_funct_2(sK4,k1_xboole_0,X0)
      | ~ sP2(k1_xboole_0,sK4,X0) ) ),
    inference(superposition,[],[f95,f527])).

fof(f527,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,sK4) ),
    inference(forward_demodulation,[],[f525,f497])).

fof(f497,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(resolution,[],[f476,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f71,f59])).

fof(f525,plain,(
    ! [X0,X1] : k1_relat_1(sK4) = k1_relset_1(X0,X1,sK4) ),
    inference(resolution,[],[f477,f81])).

fof(f95,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1)
      | v1_funct_2(X1,k1_xboole_0,X2)
      | ~ sP2(k1_xboole_0,X1,X2) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X1,X0,X2)
      | k1_relset_1(X0,X2,X1) != X0
      | k1_xboole_0 != X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f501,plain,(
    ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f442,f497])).

fof(f442,plain,(
    ~ v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f399,f441])).

fof(f441,plain,(
    ! [X0] : m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ),
    inference(subsumption_resolution,[],[f421,f59])).

fof(f421,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) ) ),
    inference(backward_demodulation,[],[f260,f401])).

fof(f399,plain,
    ( ~ v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f378,f376])).

fof(f378,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))
    | ~ v1_funct_2(sK4,k1_relat_1(sK4),sK3) ),
    inference(backward_demodulation,[],[f100,f376])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (19381)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (19373)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (19363)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (19358)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (19367)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.50  % (19364)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (19365)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (19387)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (19379)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (19371)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (19374)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (19361)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (19362)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (19382)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (19367)Refutation not found, incomplete strategy% (19367)------------------------------
% 0.20/0.53  % (19367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19367)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19367)Memory used [KB]: 10746
% 0.20/0.53  % (19367)Time elapsed: 0.127 s
% 0.20/0.53  % (19367)------------------------------
% 0.20/0.53  % (19367)------------------------------
% 0.20/0.53  % (19359)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19366)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (19385)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (19372)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (19368)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (19386)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (19368)Refutation not found, incomplete strategy% (19368)------------------------------
% 0.20/0.54  % (19368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19383)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (19380)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (19377)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (19378)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (19365)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f537,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(subsumption_resolution,[],[f501,f536])).
% 0.20/0.54  fof(f536,plain,(
% 0.20/0.54    ( ! [X0] : (v1_funct_2(sK4,k1_xboole_0,X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f535,f526])).
% 0.20/0.54  fof(f526,plain,(
% 0.20/0.54    ( ! [X2,X3] : (sP2(X2,sK4,X3)) )),
% 0.20/0.54    inference(resolution,[],[f477,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f28])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(definition_folding,[],[f23,f27])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.54  % (19375)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f477,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f440,f476])).
% 0.20/0.54  fof(f476,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_relat_1(sK4),X0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f471,f173])).
% 0.20/0.54  fof(f173,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f171,f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    ( ! [X5] : (~r2_hidden(X5,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK7(k1_xboole_0,X5))) )),
% 0.20/0.54    inference(resolution,[],[f167,f79])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f18])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,axiom,(
% 0.20/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.54  fof(f167,plain,(
% 0.20/0.54    ( ! [X1] : (r2_hidden(sK7(k1_xboole_0,X1),k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.54    inference(forward_demodulation,[],[f166,f57])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.54    inference(cnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.54  fof(f166,plain,(
% 0.20/0.54    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | r2_hidden(sK7(k1_xboole_0,X1),k1_relat_1(k1_xboole_0))) )),
% 0.20/0.54    inference(resolution,[],[f164,f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ( ! [X0,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(X5,X1) | r2_hidden(sK7(X0,X5),k1_relat_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f37,plain,(
% 0.20/0.54    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & ((sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f33,f36,f35,f34])).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK5(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = sK5(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) => (sK5(X0,X1) = k1_funct_1(X0,sK6(X0,X1)) & r2_hidden(sK6(X0,X1),k1_relat_1(X0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f36,plain,(
% 0.20/0.54    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X5)) = X5 & r2_hidden(sK7(X0,X5),k1_relat_1(X0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0)))))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.54  fof(f164,plain,(
% 0.20/0.54    sP0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.54    inference(resolution,[],[f159,f59])).
% 0.20/0.54  fof(f159,plain,(
% 0.20/0.54    ( ! [X2] : (~r1_tarski(X2,sK5(k1_xboole_0,X2)) | sP0(k1_xboole_0,X2)) )),
% 0.20/0.54    inference(resolution,[],[f157,f79])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X5] : (r2_hidden(sK5(k1_xboole_0,X5),X5) | sP0(k1_xboole_0,X5)) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f149,f59])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    ( ! [X5] : (r2_hidden(sK5(k1_xboole_0,X5),X5) | sP0(k1_xboole_0,X5) | ~r1_tarski(k1_xboole_0,sK6(k1_xboole_0,X5))) )),
% 0.20/0.54    inference(resolution,[],[f145,f79])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(sK6(k1_xboole_0,X0),k1_xboole_0) | r2_hidden(sK5(k1_xboole_0,X0),X0) | sP0(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(superposition,[],[f65,f57])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),k1_relat_1(X0)) | r2_hidden(sK5(X0,X1),X1) | sP0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f471,plain,(
% 0.20/0.54    ( ! [X0] : (r2_hidden(k1_funct_1(sK4,sK8(k1_relat_1(sK4),X0)),k1_xboole_0) | r1_tarski(k1_relat_1(sK4),X0)) )),
% 0.20/0.54    inference(resolution,[],[f439,f130])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X2) | r2_hidden(k1_funct_1(X0,sK8(k1_relat_1(X0),X1)),X2) | r1_tarski(k1_relat_1(X0),X1)) )),
% 0.20/0.54    inference(resolution,[],[f90,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f41,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f40])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f90,plain,(
% 0.20/0.54    ( ! [X6,X0,X1] : (~r2_hidden(X6,k1_relat_1(X0)) | r2_hidden(k1_funct_1(X0,X6),X1) | ~sP0(X0,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | ~sP0(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f37])).
% 0.20/0.54  fof(f439,plain,(
% 0.20/0.54    sP0(sK4,k1_xboole_0)),
% 0.20/0.54    inference(subsumption_resolution,[],[f417,f173])).
% 0.20/0.54  fof(f417,plain,(
% 0.20/0.54    r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k1_xboole_0) | sP0(sK4,k1_xboole_0)),
% 0.20/0.54    inference(backward_demodulation,[],[f244,f401])).
% 0.20/0.54  fof(f401,plain,(
% 0.20/0.54    k1_xboole_0 = k2_relat_1(sK4)),
% 0.20/0.54    inference(subsumption_resolution,[],[f400,f59])).
% 0.20/0.54  fof(f400,plain,(
% 0.20/0.54    ~r1_tarski(k1_xboole_0,k2_relat_1(sK4)) | k1_xboole_0 = k2_relat_1(sK4)),
% 0.20/0.54    inference(forward_demodulation,[],[f379,f376])).
% 0.20/0.54  fof(f376,plain,(
% 0.20/0.54    k1_xboole_0 = sK3),
% 0.20/0.54    inference(subsumption_resolution,[],[f375,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    r1_tarski(k2_relat_1(sK4),sK3)),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f14,f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1)) => ((~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)) & r1_tarski(k2_relat_1(sK4),sK3) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f14,plain,(
% 0.20/0.54    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.20/0.54    inference(flattening,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1)) & r1_tarski(k2_relat_1(X1),X0)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f12])).
% 0.20/0.54  fof(f12,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.54    inference(negated_conjecture,[],[f11])).
% 0.20/0.54  fof(f11,conjecture,(
% 0.20/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.20/0.54  fof(f375,plain,(
% 0.20/0.54    k1_xboole_0 = sK3 | ~r1_tarski(k2_relat_1(sK4),sK3)),
% 0.20/0.54    inference(resolution,[],[f374,f260])).
% 0.20/0.54  fof(f260,plain,(
% 0.20/0.54    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0))) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.20/0.54    inference(resolution,[],[f259,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.54    inference(equality_resolution,[],[f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f259,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK4),X1) | ~r1_tarski(k2_relat_1(sK4),X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.54    inference(resolution,[],[f80,f53])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    v1_relat_1(sK4)),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  % (19375)Refutation not found, incomplete strategy% (19375)------------------------------
% 0.20/0.54  % (19375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19375)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19375)Memory used [KB]: 10746
% 0.20/0.54  % (19375)Time elapsed: 0.152 s
% 0.20/0.54  % (19375)------------------------------
% 0.20/0.54  % (19375)------------------------------
% 0.20/0.55  % (19384)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (19369)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f20])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).
% 0.20/0.55  fof(f374,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | k1_xboole_0 = sK3),
% 0.20/0.55    inference(subsumption_resolution,[],[f372,f55])).
% 0.20/0.55  fof(f372,plain,(
% 0.20/0.55    k1_xboole_0 = sK3 | ~r1_tarski(k2_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 0.20/0.55    inference(resolution,[],[f371,f100])).
% 0.20/0.55  fof(f100,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3)))),
% 0.20/0.55    inference(subsumption_resolution,[],[f56,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    v1_funct_1(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f56,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK3))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3) | ~v1_funct_1(sK4)),
% 0.20/0.55    inference(cnf_transformation,[],[f30])).
% 0.20/0.55  fof(f371,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(sK4,k1_relat_1(sK4),X0) | k1_xboole_0 = X0 | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f370,f261])).
% 0.20/0.55  fof(f261,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k2_relat_1(sK4),X0) | k1_relat_1(sK4) = k1_relset_1(k1_relat_1(sK4),X0,sK4)) )),
% 0.20/0.55    inference(resolution,[],[f260,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f370,plain,(
% 0.20/0.55    ( ! [X0] : (k1_relat_1(sK4) != k1_relset_1(k1_relat_1(sK4),X0,sK4) | k1_xboole_0 = X0 | v1_funct_2(sK4,k1_relat_1(sK4),X0) | ~r1_tarski(k2_relat_1(sK4),X0)) )),
% 0.20/0.55    inference(resolution,[],[f84,f262])).
% 0.20/0.55  fof(f262,plain,(
% 0.20/0.55    ( ! [X1] : (sP2(k1_relat_1(sK4),sK4,X1) | ~r1_tarski(k2_relat_1(sK4),X1)) )),
% 0.20/0.55    inference(resolution,[],[f260,f86])).
% 0.20/0.55  fof(f84,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 = X2 | v1_funct_2(X1,X0,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP2(X0,X1,X2))),
% 0.20/0.55    inference(rectify,[],[f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP2(X0,X2,X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f27])).
% 0.20/0.55  fof(f379,plain,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(sK4) | ~r1_tarski(sK3,k2_relat_1(sK4))),
% 0.20/0.55    inference(backward_demodulation,[],[f110,f376])).
% 0.20/0.55  fof(f110,plain,(
% 0.20/0.55    ~r1_tarski(sK3,k2_relat_1(sK4)) | sK3 = k2_relat_1(sK4)),
% 0.20/0.55    inference(resolution,[],[f71,f55])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f39])).
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k2_relat_1(sK4)) | sP0(sK4,k1_xboole_0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f243,f53])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    sP0(sK4,k1_xboole_0) | r2_hidden(k1_funct_1(sK4,sK6(sK4,k1_xboole_0)),k2_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 0.20/0.55    inference(resolution,[],[f210,f54])).
% 0.20/0.55  fof(f210,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | sP0(X0,k1_xboole_0) | r2_hidden(k1_funct_1(X0,sK6(X0,k1_xboole_0)),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f188,f101])).
% 0.20/0.55  fof(f101,plain,(
% 0.20/0.55    ( ! [X0] : (sP0(X0,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(resolution,[],[f89,f68])).
% 0.20/0.55  fof(f68,plain,(
% 0.20/0.55    ( ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0] : (sP1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(definition_folding,[],[f16,f25,f24])).
% 0.20/0.55  fof(f25,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.55  fof(f89,plain,(
% 0.20/0.55    ( ! [X0] : (~sP1(X0) | sP0(X0,k2_relat_1(X0))) )),
% 0.20/0.55    inference(equality_resolution,[],[f60])).
% 0.20/0.55  fof(f60,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP0(X0,X1) | k2_relat_1(X0) != X1 | ~sP1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k2_relat_1(X0) != X1)) | ~sP1(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f25])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~sP0(X0,X1) | r2_hidden(k1_funct_1(X0,sK6(X0,k1_xboole_0)),X1) | sP0(X0,k1_xboole_0)) )),
% 0.20/0.55    inference(resolution,[],[f175,f90])).
% 0.20/0.55  fof(f175,plain,(
% 0.20/0.55    ( ! [X7] : (r2_hidden(sK6(X7,k1_xboole_0),k1_relat_1(X7)) | sP0(X7,k1_xboole_0)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f142,f173])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ( ! [X7] : (r2_hidden(sK6(X7,k1_xboole_0),k1_relat_1(X7)) | sP0(X7,k1_xboole_0) | r2_hidden(k4_tarski(sK11(k1_xboole_0,sK5(X7,k1_xboole_0)),sK5(X7,k1_xboole_0)),k1_xboole_0)) )),
% 0.20/0.55    inference(resolution,[],[f65,f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r2_hidden(k4_tarski(sK11(k1_xboole_0,X0),X0),k1_xboole_0)) )),
% 0.20/0.55    inference(superposition,[],[f94,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f5])).
% 0.20/0.55  fof(f94,plain,(
% 0.20/0.55    ( ! [X0,X5] : (~r2_hidden(X5,k2_relat_1(X0)) | r2_hidden(k4_tarski(sK11(X0,X5),X5),X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f49])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (r2_hidden(k4_tarski(sK11(X0,X5),X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f45,f48,f47,f46])).
% 0.20/0.55  fof(f46,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(X3,sK9(X0,X1)),X0) | ~r2_hidden(sK9(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) | r2_hidden(sK9(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(X4,sK9(X0,X1)),X0) => r2_hidden(k4_tarski(sK10(X0,X1),sK9(X0,X1)),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) => r2_hidden(k4_tarski(sK11(X0,X5),X5),X0))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X4,X2),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X6,X5),X0)) & (? [X7] : r2_hidden(k4_tarski(X7,X5),X0) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(rectify,[],[f44])).
% 0.20/0.55  fof(f44,plain,(
% 0.20/0.55    ! [X0,X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X3,X2),X0)) & (? [X3] : r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1))),
% 0.20/0.55    inference(nnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.55  fof(f440,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK4),X1) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f420,f59])).
% 0.20/0.55  fof(f420,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r1_tarski(k1_relat_1(sK4),X1) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f259,f401])).
% 0.20/0.55  fof(f535,plain,(
% 0.20/0.55    ( ! [X0] : (v1_funct_2(sK4,k1_xboole_0,X0) | ~sP2(k1_xboole_0,sK4,X0)) )),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f534])).
% 0.20/0.55  fof(f534,plain,(
% 0.20/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(sK4,k1_xboole_0,X0) | ~sP2(k1_xboole_0,sK4,X0)) )),
% 0.20/0.55    inference(superposition,[],[f95,f527])).
% 0.20/0.55  fof(f527,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,sK4)) )),
% 0.20/0.55    inference(forward_demodulation,[],[f525,f497])).
% 0.20/0.55  fof(f497,plain,(
% 0.20/0.55    k1_xboole_0 = k1_relat_1(sK4)),
% 0.20/0.55    inference(resolution,[],[f476,f108])).
% 0.20/0.55  fof(f108,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.55    inference(resolution,[],[f71,f59])).
% 0.20/0.55  fof(f525,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k1_relat_1(sK4) = k1_relset_1(X0,X1,sK4)) )),
% 0.20/0.55    inference(resolution,[],[f477,f81])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X2,X1) | v1_funct_2(X1,k1_xboole_0,X2) | ~sP2(k1_xboole_0,X1,X2)) )),
% 0.20/0.55    inference(equality_resolution,[],[f85])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0 | k1_xboole_0 != X0 | ~sP2(X0,X1,X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f501,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 0.20/0.55    inference(backward_demodulation,[],[f442,f497])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0)),
% 0.20/0.55    inference(subsumption_resolution,[],[f399,f441])).
% 0.20/0.55  fof(f441,plain,(
% 0.20/0.55    ( ! [X0] : (m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f421,f59])).
% 0.20/0.55  fof(f421,plain,(
% 0.20/0.55    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),X0)))) )),
% 0.20/0.55    inference(backward_demodulation,[],[f260,f401])).
% 0.20/0.55  fof(f399,plain,(
% 0.20/0.55    ~v1_funct_2(sK4,k1_relat_1(sK4),k1_xboole_0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0)))),
% 0.20/0.55    inference(forward_demodulation,[],[f378,f376])).
% 0.20/0.55  fof(f378,plain,(
% 0.20/0.55    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k1_xboole_0))) | ~v1_funct_2(sK4,k1_relat_1(sK4),sK3)),
% 0.20/0.55    inference(backward_demodulation,[],[f100,f376])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (19365)------------------------------
% 0.20/0.55  % (19365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (19365)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (19365)Memory used [KB]: 6652
% 0.20/0.55  % (19365)Time elapsed: 0.094 s
% 0.20/0.55  % (19365)------------------------------
% 0.20/0.55  % (19365)------------------------------
% 0.20/0.55  % (19370)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (19368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (19368)Memory used [KB]: 10746
% 0.20/0.55  % (19368)Time elapsed: 0.126 s
% 0.20/0.55  % (19368)------------------------------
% 0.20/0.55  % (19368)------------------------------
% 0.20/0.55  % (19357)Success in time 0.196 s
%------------------------------------------------------------------------------
