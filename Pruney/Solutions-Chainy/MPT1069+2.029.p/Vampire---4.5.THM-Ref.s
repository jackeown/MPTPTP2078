%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 387 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :   28
%              Number of atoms          :  592 (3089 expanded)
%              Number of equality atoms :  123 ( 704 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f81,f79,f320,f206])).

fof(f206,plain,(
    ! [X2,X1] :
      ( X1 = X2
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f145,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f100,f92])).

fof(f92,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK14(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f57,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK14(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
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

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK15(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK15(X0,X1),X1)
          & r2_hidden(sK15(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK15(X0,X1),X1)
        & r2_hidden(sK15(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f145,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f98,f129])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f320,plain,(
    v1_xboole_0(sK7) ),
    inference(subsumption_resolution,[],[f297,f81])).

fof(f297,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK7) ),
    inference(superposition,[],[f71,f293])).

fof(f293,plain,
    ( k1_xboole_0 = sK8
    | v1_xboole_0(sK7) ),
    inference(resolution,[],[f281,f111])).

% (22530)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f111,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f281,plain,
    ( sP3(sK7,sK8)
    | v1_xboole_0(sK7) ),
    inference(resolution,[],[f278,f126])).

fof(f126,plain,
    ( r2_hidden(sK11,sK7)
    | v1_xboole_0(sK7) ),
    inference(resolution,[],[f94,f77])).

fof(f77,plain,(
    m1_subset_1(sK11,sK7) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
    & k1_xboole_0 != sK7
    & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    & m1_subset_1(sK11,sK7)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    & v1_funct_1(sK10)
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK9,sK7,sK8)
    & v1_funct_1(sK9)
    & ~ v1_xboole_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f18,f45,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK7
                  & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                  & m1_subset_1(X5,sK7) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
          & v1_funct_2(X3,sK7,sK8)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK7
                & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4))
                & m1_subset_1(X5,sK7) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
        & v1_funct_2(X3,sK7,sK8)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5))
              & k1_xboole_0 != sK7
              & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4))
              & m1_subset_1(X5,sK7) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK9,sK7,sK8)
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5))
            & k1_xboole_0 != sK7
            & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4))
            & m1_subset_1(X5,sK7) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5))
          & k1_xboole_0 != sK7
          & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
          & m1_subset_1(X5,sK7) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5))
        & k1_xboole_0 != sK7
        & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
        & m1_subset_1(X5,sK7) )
   => ( k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))
      & k1_xboole_0 != sK7
      & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
      & m1_subset_1(sK11,sK7) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

% (22531)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f278,plain,
    ( ~ r2_hidden(sK11,sK7)
    | sP3(sK7,sK8) ),
    inference(superposition,[],[f254,f253])).

fof(f253,plain,
    ( sK7 = k1_relat_1(sK9)
    | sP3(sK7,sK8) ),
    inference(subsumption_resolution,[],[f251,f73])).

fof(f73,plain,(
    v1_funct_2(sK9,sK7,sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f251,plain,
    ( ~ v1_funct_2(sK9,sK7,sK8)
    | sP3(sK7,sK8)
    | sK7 = k1_relat_1(sK9) ),
    inference(resolution,[],[f179,f74])).

fof(f74,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f46])).

fof(f179,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f175,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X2,X1,X0)
        & sP4(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f33,f40,f39,f38])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f175,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | ~ sP4(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f109,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

% (22530)Refutation not found, incomplete strategy% (22530)------------------------------
% (22530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22530)Termination reason: Refutation not found, incomplete strategy

% (22530)Memory used [KB]: 10874
% (22530)Time elapsed: 0.141 s
% (22530)------------------------------
% (22530)------------------------------
fof(f254,plain,(
    ~ r2_hidden(sK11,k1_relat_1(sK9)) ),
    inference(resolution,[],[f250,f116])).

fof(f116,plain,(
    ! [X2,X1] :
      ( sP0(k1_funct_1(X1,X2),X1)
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1)
      | k1_funct_1(X1,X2) != X0
      | ~ r2_hidden(X2,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ( k1_funct_1(X1,sK13(X0,X1)) = X0
          & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) = X0
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X1,sK13(X0,X1)) = X0
        & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ! [X2] :
            ( k1_funct_1(X1,X2) != X0
            | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X1,X3) = X0
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ( sP0(X2,X0)
        | ! [X3] :
            ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
      & ( ? [X3] :
            ( k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ~ sP0(X2,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X0] :
      ( sP0(X2,X0)
    <=> ? [X3] :
          ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f250,plain,(
    ~ sP0(k1_funct_1(sK9,sK11),sK9) ),
    inference(resolution,[],[f244,f232])).

fof(f232,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK10))
      | ~ sP0(X0,sK9) ) ),
    inference(subsumption_resolution,[],[f228,f135])).

fof(f135,plain,(
    sP2(sK9) ),
    inference(resolution,[],[f133,f123])).

fof(f123,plain,
    ( ~ v1_relat_1(sK9)
    | sP2(sK9) ),
    inference(resolution,[],[f91,f72])).

fof(f72,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f46])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | sP2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f20,f36,f35,f34])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> sP0(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> sP1(X0,X1) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f133,plain,(
    v1_relat_1(sK9) ),
    inference(resolution,[],[f103,f74])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

% (22547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f228,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_relat_1(sK10))
      | ~ sP0(X0,sK9)
      | ~ sP2(sK9) ) ),
    inference(resolution,[],[f171,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | ~ sP0(X0,X1)
      | ~ sP2(X1) ) ),
    inference(resolution,[],[f85,f115])).

fof(f115,plain,(
    ! [X0] :
      ( sP1(X0,k2_relat_1(X0))
      | ~ sP2(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | k2_relat_1(X0) != X1
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ~ sP1(X0,X1) )
          & ( sP1(X0,X1)
            | k2_relat_1(X0) != X1 ) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ sP1(X0,X1)
      | ~ sP0(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( ~ sP0(sK12(X0,X1),X0)
            | ~ r2_hidden(sK12(X0,X1),X1) )
          & ( sP0(sK12(X0,X1),X0)
            | r2_hidden(sK12(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f49,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ sP0(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( sP0(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ sP0(sK12(X0,X1),X0)
          | ~ r2_hidden(sK12(X0,X1),X1) )
        & ( sP0(sK12(X0,X1),X0)
          | r2_hidden(sK12(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ sP0(X3,X0) )
            & ( sP0(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2] :
            ( ( ~ sP0(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( sP0(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ sP0(X2,X0) )
            & ( sP0(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f171,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK9))
      | r2_hidden(X0,k1_relat_1(sK10)) ) ),
    inference(resolution,[],[f170,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f170,plain,(
    r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) ),
    inference(subsumption_resolution,[],[f168,f76])).

% (22544)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f76,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(cnf_transformation,[],[f46])).

fof(f168,plain,
    ( r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) ),
    inference(superposition,[],[f162,f105])).

fof(f162,plain,(
    r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(subsumption_resolution,[],[f161,f74])).

fof(f161,plain,
    ( r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(superposition,[],[f78,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f78,plain,(
    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) ),
    inference(cnf_transformation,[],[f46])).

% (22543)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f244,plain,(
    ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) ),
    inference(subsumption_resolution,[],[f243,f134])).

fof(f134,plain,(
    v1_relat_1(sK10) ),
    inference(resolution,[],[f103,f76])).

fof(f243,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f242,f151])).

fof(f151,plain,(
    v5_relat_1(sK10,sK6) ),
    inference(resolution,[],[f106,f76])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f242,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f241,f75])).

fof(f75,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f46])).

fof(f241,plain,
    ( ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10) ),
    inference(trivial_inequality_removal,[],[f240])).

fof(f240,plain,
    ( k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v5_relat_1(sK10,sK6)
    | ~ v1_relat_1(sK10) ),
    inference(superposition,[],[f204,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

fof(f204,plain,(
    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) ),
    inference(subsumption_resolution,[],[f203,f71])).

fof(f203,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f202,f72])).

fof(f202,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f201,f73])).

fof(f201,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f200,f74])).

fof(f200,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f199,f75])).

fof(f199,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f198,f76])).

fof(f198,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f197,f77])).

fof(f197,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ m1_subset_1(sK11,sK7)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f196,f78])).

fof(f196,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK11,sK7)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(subsumption_resolution,[],[f193,f79])).

fof(f193,plain,
    ( k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))
    | k1_xboole_0 = sK7
    | ~ r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))
    | ~ m1_subset_1(sK11,sK7)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))
    | ~ v1_funct_1(sK10)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | ~ v1_funct_2(sK9,sK7,sK8)
    | ~ v1_funct_1(sK9)
    | v1_xboole_0(sK8) ),
    inference(superposition,[],[f80,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f80,plain,(
    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) ),
    inference(cnf_transformation,[],[f46])).

fof(f71,plain,(
    ~ v1_xboole_0(sK8) ),
    inference(cnf_transformation,[],[f46])).

fof(f79,plain,(
    k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f46])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:51:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (22533)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (22521)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (22540)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (22549)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (22527)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (22520)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (22523)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (22541)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (22524)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (22549)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.53  % (22542)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (22535)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (22534)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (22522)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (22545)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (22546)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (22525)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (22537)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (22548)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (22538)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (22532)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (22526)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (22529)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (22528)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f329,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f81,f79,f320,f206])).
% 0.20/0.54  fof(f206,plain,(
% 0.20/0.54    ( ! [X2,X1] : (X1 = X2 | ~v1_xboole_0(X2) | ~v1_xboole_0(X1)) )),
% 0.20/0.54    inference(resolution,[],[f145,f129])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(resolution,[],[f100,f92])).
% 0.20/0.54  fof(f92,plain,(
% 0.20/0.54    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f59])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK14(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f57,f58])).
% 0.20/0.54  fof(f58,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK14(X0),X0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f57,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(rectify,[],[f56])).
% 0.20/0.54  fof(f56,plain,(
% 0.20/0.54    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.54    inference(nnf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.54  fof(f100,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r2_hidden(sK15(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f65])).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK15(X0,X1),X1) & r2_hidden(sK15(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f63,f64])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK15(X0,X1),X1) & r2_hidden(sK15(X0,X1),X0)))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f63,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(rectify,[],[f62])).
% 0.20/0.54  fof(f62,plain,(
% 0.20/0.54    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.54    inference(nnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    ( ! [X2,X1] : (~r1_tarski(X1,X2) | X1 = X2 | ~v1_xboole_0(X2)) )),
% 0.20/0.54    inference(resolution,[],[f98,f129])).
% 0.20/0.54  fof(f98,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(flattening,[],[f60])).
% 0.20/0.54  fof(f60,plain,(
% 0.20/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.54  fof(f320,plain,(
% 0.20/0.54    v1_xboole_0(sK7)),
% 0.20/0.54    inference(subsumption_resolution,[],[f297,f81])).
% 0.20/0.54  fof(f297,plain,(
% 0.20/0.54    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK7)),
% 0.20/0.54    inference(superposition,[],[f71,f293])).
% 0.20/0.54  fof(f293,plain,(
% 0.20/0.54    k1_xboole_0 = sK8 | v1_xboole_0(sK7)),
% 0.20/0.54    inference(resolution,[],[f281,f111])).
% 0.20/0.54  % (22530)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  fof(f111,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sP3(X0,X1) | k1_xboole_0 = X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f70])).
% 0.20/0.54  fof(f70,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.54  fof(f281,plain,(
% 0.20/0.54    sP3(sK7,sK8) | v1_xboole_0(sK7)),
% 0.20/0.54    inference(resolution,[],[f278,f126])).
% 0.20/0.54  fof(f126,plain,(
% 0.20/0.54    r2_hidden(sK11,sK7) | v1_xboole_0(sK7)),
% 0.20/0.54    inference(resolution,[],[f94,f77])).
% 0.20/0.54  fof(f77,plain,(
% 0.20/0.54    m1_subset_1(sK11,sK7)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    (((k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9)) & ~v1_xboole_0(sK8)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10,sK11])],[f18,f45,f44,f43,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) & ~v1_xboole_0(sK8))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,X3,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,X3),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(X3,sK7,sK8) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK9,sK7,sK8) & v1_funct_1(sK9))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,X4),X5) != k7_partfun1(sK6,X4,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,X4)) & m1_subset_1(X5,sK7)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(X5,sK7)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) & v1_funct_1(sK10))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    ? [X5] : (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),X5) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,X5)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(X5,sK7)) => (k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) & k1_xboole_0 != sK7 & r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) & m1_subset_1(sK11,sK7))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f18,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.20/0.54    inference(flattening,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.20/0.54    inference(ennf_transformation,[],[f15])).
% 0.20/0.54  % (22531)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  fof(f15,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.54    inference(negated_conjecture,[],[f14])).
% 0.20/0.54  fof(f14,conjecture,(
% 0.20/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.54  fof(f278,plain,(
% 0.20/0.54    ~r2_hidden(sK11,sK7) | sP3(sK7,sK8)),
% 0.20/0.54    inference(superposition,[],[f254,f253])).
% 0.20/0.54  fof(f253,plain,(
% 0.20/0.54    sK7 = k1_relat_1(sK9) | sP3(sK7,sK8)),
% 0.20/0.54    inference(subsumption_resolution,[],[f251,f73])).
% 0.20/0.54  fof(f73,plain,(
% 0.20/0.54    v1_funct_2(sK9,sK7,sK8)),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f251,plain,(
% 0.20/0.54    ~v1_funct_2(sK9,sK7,sK8) | sP3(sK7,sK8) | sK7 = k1_relat_1(sK9)),
% 0.20/0.54    inference(resolution,[],[f179,f74])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.20/0.54    inference(cnf_transformation,[],[f46])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f175,f113])).
% 0.20/0.54  fof(f113,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((sP5(X2,X1,X0) & sP4(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(definition_folding,[],[f33,f40,f39,f38])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.54  fof(f40,plain,(
% 0.20/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 0.20/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(flattening,[],[f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.54  fof(f175,plain,(
% 0.20/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | ~sP4(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.20/0.54    inference(superposition,[],[f109,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f9])).
% 0.20/0.54  fof(f9,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP3(X0,X2) | ~sP4(X0,X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f69])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP3(X0,X2) | ~sP4(X0,X1,X2))),
% 0.20/0.54    inference(rectify,[],[f68])).
% 0.20/0.54  fof(f68,plain,(
% 0.20/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 0.20/0.54    inference(nnf_transformation,[],[f39])).
% 0.20/0.54  % (22530)Refutation not found, incomplete strategy% (22530)------------------------------
% 0.20/0.54  % (22530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22530)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22530)Memory used [KB]: 10874
% 0.20/0.54  % (22530)Time elapsed: 0.141 s
% 0.20/0.54  % (22530)------------------------------
% 0.20/0.54  % (22530)------------------------------
% 0.20/0.55  fof(f254,plain,(
% 0.20/0.55    ~r2_hidden(sK11,k1_relat_1(sK9))),
% 0.20/0.55    inference(resolution,[],[f250,f116])).
% 0.20/0.55  fof(f116,plain,(
% 0.20/0.55    ( ! [X2,X1] : (sP0(k1_funct_1(X1,X2),X1) | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.55    inference(equality_resolution,[],[f90])).
% 0.20/0.55  fof(f90,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (sP0(X0,X1) | k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f55])).
% 0.20/0.55  fof(f55,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & ((k1_funct_1(X1,sK13(X0,X1)) = X0 & r2_hidden(sK13(X0,X1),k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f53,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) => (k1_funct_1(X1,sK13(X0,X1)) = X0 & r2_hidden(sK13(X0,X1),k1_relat_1(X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP0(X0,X1) | ! [X2] : (k1_funct_1(X1,X2) != X0 | ~r2_hidden(X2,k1_relat_1(X1)))) & (? [X3] : (k1_funct_1(X1,X3) = X0 & r2_hidden(X3,k1_relat_1(X1))) | ~sP0(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f52])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    ! [X2,X0] : ((sP0(X2,X0) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~sP0(X2,X0)))),
% 0.20/0.55    inference(nnf_transformation,[],[f34])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ! [X2,X0] : (sP0(X2,X0) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    ~sP0(k1_funct_1(sK9,sK11),sK9)),
% 0.20/0.55    inference(resolution,[],[f244,f232])).
% 0.20/0.55  fof(f232,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK10)) | ~sP0(X0,sK9)) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f228,f135])).
% 0.20/0.55  fof(f135,plain,(
% 0.20/0.55    sP2(sK9)),
% 0.20/0.55    inference(resolution,[],[f133,f123])).
% 0.20/0.55  fof(f123,plain,(
% 0.20/0.55    ~v1_relat_1(sK9) | sP2(sK9)),
% 0.20/0.55    inference(resolution,[],[f91,f72])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    v1_funct_1(sK9)),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f91,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_funct_1(X0) | sP2(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f37])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    ! [X0] : (sP2(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(definition_folding,[],[f20,f36,f35,f34])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ! [X0,X1] : (sP1(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> sP0(X2,X0)))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> sP1(X0,X1)) | ~sP2(X0))),
% 0.20/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(flattening,[],[f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 0.20/0.55  fof(f133,plain,(
% 0.20/0.55    v1_relat_1(sK9)),
% 0.20/0.55    inference(resolution,[],[f103,f74])).
% 0.20/0.55  fof(f103,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  % (22547)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.55  fof(f228,plain,(
% 0.20/0.55    ( ! [X0] : (r2_hidden(X0,k1_relat_1(sK10)) | ~sP0(X0,sK9) | ~sP2(sK9)) )),
% 0.20/0.55    inference(resolution,[],[f171,f142])).
% 0.20/0.55  fof(f142,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(X1)) | ~sP0(X0,X1) | ~sP2(X1)) )),
% 0.20/0.55    inference(resolution,[],[f85,f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    ( ! [X0] : (sP1(X0,k2_relat_1(X0)) | ~sP2(X0)) )),
% 0.20/0.55    inference(equality_resolution,[],[f82])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sP1(X0,X1) | k2_relat_1(X0) != X1 | ~sP2(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f47])).
% 0.20/0.55  fof(f47,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ~sP1(X0,X1)) & (sP1(X0,X1) | k2_relat_1(X0) != X1)) | ~sP2(X0))),
% 0.20/0.55    inference(nnf_transformation,[],[f36])).
% 0.20/0.55  fof(f85,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~sP1(X0,X1) | ~sP0(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f51])).
% 0.20/0.55  fof(f51,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | ((~sP0(sK12(X0,X1),X0) | ~r2_hidden(sK12(X0,X1),X1)) & (sP0(sK12(X0,X1),X0) | r2_hidden(sK12(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f49,f50])).
% 0.20/0.55  fof(f50,plain,(
% 0.20/0.55    ! [X1,X0] : (? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1))) => ((~sP0(sK12(X0,X1),X0) | ~r2_hidden(sK12(X0,X1),X1)) & (sP0(sK12(X0,X1),X0) | r2_hidden(sK12(X0,X1),X1))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~sP0(X3,X0)) & (sP0(X3,X0) | ~r2_hidden(X3,X1))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(rectify,[],[f48])).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ! [X0,X1] : ((sP1(X0,X1) | ? [X2] : ((~sP0(X2,X0) | ~r2_hidden(X2,X1)) & (sP0(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~sP0(X2,X0)) & (sP0(X2,X0) | ~r2_hidden(X2,X1))) | ~sP1(X0,X1)))),
% 0.20/0.55    inference(nnf_transformation,[],[f35])).
% 0.20/0.55  fof(f171,plain,(
% 0.20/0.55    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK9)) | r2_hidden(X0,k1_relat_1(sK10))) )),
% 0.20/0.55    inference(resolution,[],[f170,f99])).
% 0.20/0.55  fof(f99,plain,(
% 0.20/0.55    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f65])).
% 0.20/0.55  fof(f170,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10))),
% 0.20/0.55    inference(subsumption_resolution,[],[f168,f76])).
% 0.20/0.55  % (22544)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f168,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(sK9),k1_relat_1(sK10)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6)))),
% 0.20/0.55    inference(superposition,[],[f162,f105])).
% 0.20/0.55  fof(f162,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10))),
% 0.20/0.55    inference(subsumption_resolution,[],[f161,f74])).
% 0.20/0.55  fof(f161,plain,(
% 0.20/0.55    r1_tarski(k2_relat_1(sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 0.20/0.55    inference(superposition,[],[f78,f104])).
% 0.20/0.55  fof(f104,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f10])).
% 0.20/0.55  fof(f10,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10))),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  % (22543)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  fof(f244,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10))),
% 0.20/0.55    inference(subsumption_resolution,[],[f243,f134])).
% 0.20/0.55  fof(f134,plain,(
% 0.20/0.55    v1_relat_1(sK10)),
% 0.20/0.55    inference(resolution,[],[f103,f76])).
% 0.20/0.55  fof(f243,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_relat_1(sK10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f242,f151])).
% 0.20/0.55  fof(f151,plain,(
% 0.20/0.55    v5_relat_1(sK10,sK6)),
% 0.20/0.55    inference(resolution,[],[f106,f76])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f31])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.20/0.55    inference(pure_predicate_removal,[],[f8])).
% 0.20/0.55  fof(f8,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.55  fof(f242,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10)),
% 0.20/0.55    inference(subsumption_resolution,[],[f241,f75])).
% 0.20/0.55  fof(f75,plain,(
% 0.20/0.55    v1_funct_1(sK10)),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f241,plain,(
% 0.20/0.55    ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10)),
% 0.20/0.55    inference(trivial_inequality_removal,[],[f240])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    k1_funct_1(sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r2_hidden(k1_funct_1(sK9,sK11),k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v5_relat_1(sK10,sK6) | ~v1_relat_1(sK10)),
% 0.20/0.55    inference(superposition,[],[f204,f95])).
% 0.20/0.55  fof(f95,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f24])).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.55    inference(flattening,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,axiom,(
% 0.20/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).
% 0.20/0.55  fof(f204,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11))),
% 0.20/0.55    inference(subsumption_resolution,[],[f203,f71])).
% 0.20/0.55  fof(f203,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f202,f72])).
% 0.20/0.55  fof(f202,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f201,f73])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f200,f74])).
% 0.20/0.55  fof(f200,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f199,f75])).
% 0.20/0.55  fof(f199,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f198,f76])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f197,f77])).
% 0.20/0.55  fof(f197,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~m1_subset_1(sK11,sK7) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f196,f78])).
% 0.20/0.55  fof(f196,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK11,sK7) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(subsumption_resolution,[],[f193,f79])).
% 0.20/0.55  fof(f193,plain,(
% 0.20/0.55    k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11)) != k1_funct_1(sK10,k1_funct_1(sK9,sK11)) | k1_xboole_0 = sK7 | ~r1_tarski(k2_relset_1(sK7,sK8,sK9),k1_relset_1(sK8,sK6,sK10)) | ~m1_subset_1(sK11,sK7) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK6))) | ~v1_funct_1(sK10) | ~m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) | ~v1_funct_2(sK9,sK7,sK8) | ~v1_funct_1(sK9) | v1_xboole_0(sK8)),
% 0.20/0.55    inference(superposition,[],[f80,f102])).
% 0.20/0.55  fof(f102,plain,(
% 0.20/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.20/0.55    inference(flattening,[],[f26])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.20/0.55    inference(ennf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.20/0.55  fof(f80,plain,(
% 0.20/0.55    k1_funct_1(k8_funct_2(sK7,sK8,sK6,sK9,sK10),sK11) != k7_partfun1(sK6,sK10,k1_funct_1(sK9,sK11))),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    ~v1_xboole_0(sK8)),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f79,plain,(
% 0.20/0.55    k1_xboole_0 != sK7),
% 0.20/0.55    inference(cnf_transformation,[],[f46])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    v1_xboole_0(k1_xboole_0)),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (22549)------------------------------
% 0.20/0.55  % (22549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (22549)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (22549)Memory used [KB]: 1918
% 0.20/0.55  % (22549)Time elapsed: 0.118 s
% 0.20/0.55  % (22549)------------------------------
% 0.20/0.55  % (22549)------------------------------
% 0.20/0.55  % (22536)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (22519)Success in time 0.196 s
%------------------------------------------------------------------------------
