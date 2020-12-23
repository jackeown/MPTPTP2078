%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0363+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 115 expanded)
%              Number of leaves         :    9 (  32 expanded)
%              Depth                    :   15
%              Number of atoms          :  146 ( 516 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1716,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1715,f1505])).

fof(f1505,plain,(
    ~ r1_tarski(sK20,sK19) ),
    inference(subsumption_resolution,[],[f1499,f1467])).

fof(f1467,plain,(
    r1_xboole_0(sK20,sK21) ),
    inference(subsumption_resolution,[],[f1466,f946])).

fof(f946,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f594])).

fof(f594,plain,(
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

fof(f1466,plain,
    ( r1_tarski(sK20,k4_xboole_0(sK19,sK21))
    | r1_xboole_0(sK20,sK21) ),
    inference(subsumption_resolution,[],[f1464,f859])).

fof(f859,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(sK19)) ),
    inference(cnf_transformation,[],[f727])).

fof(f727,plain,
    ( ( ~ r1_tarski(sK20,k3_subset_1(sK19,sK21))
      | ~ r1_xboole_0(sK20,sK21) )
    & ( r1_tarski(sK20,k3_subset_1(sK19,sK21))
      | r1_xboole_0(sK20,sK21) )
    & m1_subset_1(sK21,k1_zfmisc_1(sK19))
    & m1_subset_1(sK20,k1_zfmisc_1(sK19)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f724,f726,f725])).

fof(f725,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | r1_xboole_0(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK20,k3_subset_1(sK19,X2))
            | ~ r1_xboole_0(sK20,X2) )
          & ( r1_tarski(sK20,k3_subset_1(sK19,X2))
            | r1_xboole_0(sK20,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK19)) )
      & m1_subset_1(sK20,k1_zfmisc_1(sK19)) ) ),
    introduced(choice_axiom,[])).

fof(f726,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK20,k3_subset_1(sK19,X2))
          | ~ r1_xboole_0(sK20,X2) )
        & ( r1_tarski(sK20,k3_subset_1(sK19,X2))
          | r1_xboole_0(sK20,X2) )
        & m1_subset_1(X2,k1_zfmisc_1(sK19)) )
   => ( ( ~ r1_tarski(sK20,k3_subset_1(sK19,sK21))
        | ~ r1_xboole_0(sK20,sK21) )
      & ( r1_tarski(sK20,k3_subset_1(sK19,sK21))
        | r1_xboole_0(sK20,sK21) )
      & m1_subset_1(sK21,k1_zfmisc_1(sK19)) ) ),
    introduced(choice_axiom,[])).

fof(f724,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f723])).

fof(f723,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,k3_subset_1(X0,X2))
            | ~ r1_xboole_0(X1,X2) )
          & ( r1_tarski(X1,k3_subset_1(X0,X2))
            | r1_xboole_0(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f513])).

fof(f513,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_xboole_0(X1,X2)
          <~> r1_tarski(X1,k3_subset_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f505,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_xboole_0(X1,X2)
            <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f504])).

fof(f504,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f1464,plain,
    ( r1_tarski(sK20,k4_xboole_0(sK19,sK21))
    | r1_xboole_0(sK20,sK21)
    | ~ m1_subset_1(sK21,k1_zfmisc_1(sK19)) ),
    inference(superposition,[],[f860,f920])).

fof(f920,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f458])).

fof(f458,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f860,plain,
    ( r1_tarski(sK20,k3_subset_1(sK19,sK21))
    | r1_xboole_0(sK20,sK21) ),
    inference(cnf_transformation,[],[f727])).

fof(f1499,plain,
    ( ~ r1_xboole_0(sK20,sK21)
    | ~ r1_tarski(sK20,sK19) ),
    inference(resolution,[],[f1494,f943])).

fof(f943,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f591])).

fof(f591,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f590])).

fof(f590,plain,(
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

fof(f1494,plain,(
    ~ r1_tarski(sK20,k4_xboole_0(sK19,sK21)) ),
    inference(subsumption_resolution,[],[f1491,f859])).

fof(f1491,plain,
    ( ~ r1_tarski(sK20,k4_xboole_0(sK19,sK21))
    | ~ m1_subset_1(sK21,k1_zfmisc_1(sK19)) ),
    inference(superposition,[],[f1487,f920])).

fof(f1487,plain,(
    ~ r1_tarski(sK20,k3_subset_1(sK19,sK21)) ),
    inference(subsumption_resolution,[],[f861,f1467])).

fof(f861,plain,
    ( ~ r1_tarski(sK20,k3_subset_1(sK19,sK21))
    | ~ r1_xboole_0(sK20,sK21) ),
    inference(cnf_transformation,[],[f727])).

fof(f1715,plain,(
    r1_tarski(sK20,sK19) ),
    inference(duplicate_literal_removal,[],[f1714])).

fof(f1714,plain,
    ( r1_tarski(sK20,sK19)
    | r1_tarski(sK20,sK19) ),
    inference(resolution,[],[f1444,f899])).

fof(f899,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK24(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f741])).

fof(f741,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK24(X0,X1),X1)
          & r2_hidden(sK24(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f739,f740])).

fof(f740,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK24(X0,X1),X1)
        & r2_hidden(sK24(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f739,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f738])).

fof(f738,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f549])).

fof(f549,plain,(
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

fof(f1444,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK24(X1,sK19),sK20)
      | r1_tarski(X1,sK19) ) ),
    inference(resolution,[],[f1439,f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK24(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f741])).

fof(f1439,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK19)
      | ~ r2_hidden(X0,sK20) ) ),
    inference(resolution,[],[f858,f990])).

fof(f990,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f618])).

fof(f618,plain,(
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

fof(f858,plain,(
    m1_subset_1(sK20,k1_zfmisc_1(sK19)) ),
    inference(cnf_transformation,[],[f727])).
%------------------------------------------------------------------------------
