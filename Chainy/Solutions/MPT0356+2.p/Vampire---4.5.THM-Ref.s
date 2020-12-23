%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0356+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:25 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   48 (  86 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 302 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1868,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1867,f1478])).

fof(f1478,plain,(
    ~ r1_tarski(sK21,sK19) ),
    inference(subsumption_resolution,[],[f1475,f1434])).

fof(f1434,plain,(
    r1_xboole_0(sK20,sK21) ),
    inference(resolution,[],[f1429,f1204])).

fof(f1204,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f663])).

fof(f663,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f1429,plain,(
    r1_tarski(sK20,k4_xboole_0(sK19,sK21)) ),
    inference(subsumption_resolution,[],[f1428,f845])).

fof(f845,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(sK19)) ),
    inference(cnf_transformation,[],[f713])).

fof(f713,plain,
    ( ~ r1_tarski(sK21,k3_subset_1(sK19,sK20))
    & r1_tarski(sK20,k3_subset_1(sK19,sK21))
    & m1_subset_1(sK21,k1_zfmisc_1(sK19))
    & m1_subset_1(sK20,k1_zfmisc_1(sK19)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f507,f712,f711])).

fof(f711,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
            & r1_tarski(X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(sK19,sK20))
          & r1_tarski(sK20,k3_subset_1(sK19,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK19)) )
      & m1_subset_1(sK20,k1_zfmisc_1(sK19)) ) ),
    introduced(choice_axiom,[])).

% (24163)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
fof(f712,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,k3_subset_1(sK19,sK20))
        & r1_tarski(sK20,k3_subset_1(sK19,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK19)) )
   => ( ~ r1_tarski(sK21,k3_subset_1(sK19,sK20))
      & r1_tarski(sK20,k3_subset_1(sK19,sK21))
      & m1_subset_1(sK21,k1_zfmisc_1(sK19)) ) ),
    introduced(choice_axiom,[])).

fof(f507,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f506])).

fof(f506,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,k3_subset_1(X0,X1))
          & r1_tarski(X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f498])).

fof(f498,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,k3_subset_1(X0,X2))
             => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f497])).

fof(f497,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f1428,plain,
    ( r1_tarski(sK20,k4_xboole_0(sK19,sK21))
    | ~ m1_subset_1(sK21,k1_zfmisc_1(sK19)) ),
    inference(superposition,[],[f846,f903])).

fof(f903,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f553])).

fof(f553,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f846,plain,(
    r1_tarski(sK20,k3_subset_1(sK19,sK21)) ),
    inference(cnf_transformation,[],[f713])).

fof(f1475,plain,
    ( ~ r1_tarski(sK21,sK19)
    | ~ r1_xboole_0(sK20,sK21) ),
    inference(resolution,[],[f1446,f1218])).

fof(f1218,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f673])).

fof(f673,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1446,plain,
    ( ~ r1_xboole_0(sK21,sK20)
    | ~ r1_tarski(sK21,sK19) ),
    inference(resolution,[],[f1432,f1201])).

fof(f1201,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f660])).

fof(f660,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f659])).

fof(f659,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f156])).

fof(f156,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1432,plain,(
    ~ r1_tarski(sK21,k4_xboole_0(sK19,sK20)) ),
    inference(subsumption_resolution,[],[f1431,f844])).

fof(f844,plain,(
    m1_subset_1(sK20,k1_zfmisc_1(sK19)) ),
    inference(cnf_transformation,[],[f713])).

fof(f1431,plain,
    ( ~ r1_tarski(sK21,k4_xboole_0(sK19,sK20))
    | ~ m1_subset_1(sK20,k1_zfmisc_1(sK19)) ),
    inference(superposition,[],[f847,f903])).

fof(f847,plain,(
    ~ r1_tarski(sK21,k3_subset_1(sK19,sK20)) ),
    inference(cnf_transformation,[],[f713])).

fof(f1867,plain,(
    r1_tarski(sK21,sK19) ),
    inference(duplicate_literal_removal,[],[f1866])).

fof(f1866,plain,
    ( r1_tarski(sK21,sK19)
    | r1_tarski(sK21,sK19) ),
    inference(resolution,[],[f1459,f885])).

fof(f885,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK24(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f727])).

fof(f727,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK24(X0,X1),X1)
          & r2_hidden(sK24(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f725,f726])).

fof(f726,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK24(X0,X1),X1)
        & r2_hidden(sK24(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f725,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f724])).

fof(f724,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f543])).

fof(f543,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1459,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK24(X1,sK19),sK21)
      | r1_tarski(X1,sK19) ) ),
    inference(resolution,[],[f1424,f886])).

fof(f886,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK24(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f727])).

fof(f1424,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK19)
      | ~ r2_hidden(X0,sK21) ) ),
    inference(resolution,[],[f845,f913])).

fof(f913,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f559])).

fof(f559,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f476])).

fof(f476,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
%------------------------------------------------------------------------------
