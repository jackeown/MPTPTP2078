%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0372+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 5.89s
% Output     : Refutation 5.89s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 266 expanded)
%              Number of leaves         :    6 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  152 (1802 expanded)
%              Number of equality atoms :   18 ( 252 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12034,plain,(
    $false ),
    inference(subsumption_resolution,[],[f12033,f12032])).

fof(f12032,plain,(
    ~ r2_hidden(sK25(sK21,sK22,sK23),sK22) ),
    inference(subsumption_resolution,[],[f7202,f12031])).

fof(f12031,plain,(
    r2_hidden(sK25(sK21,sK22,sK23),sK23) ),
    inference(subsumption_resolution,[],[f12029,f7203])).

fof(f7203,plain,
    ( r2_hidden(sK25(sK21,sK22,sK23),sK22)
    | r2_hidden(sK25(sK21,sK22,sK23),sK23) ),
    inference(resolution,[],[f2092,f879])).

fof(f879,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK21)
      | r2_hidden(X3,sK22)
      | r2_hidden(X3,sK23) ) ),
    inference(cnf_transformation,[],[f734])).

fof(f734,plain,
    ( sK22 != k3_subset_1(sK21,sK23)
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK23)
            | ~ r2_hidden(X3,sK22) )
          & ( r2_hidden(X3,sK23)
            | r2_hidden(X3,sK22) ) )
        | ~ m1_subset_1(X3,sK21) )
    & m1_subset_1(sK23,k1_zfmisc_1(sK21))
    & m1_subset_1(sK22,k1_zfmisc_1(sK21)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21,sK22,sK23])],[f731,f733,f732])).

fof(f732,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK22 != k3_subset_1(sK21,X2)
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK22) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK22) ) )
              | ~ m1_subset_1(X3,sK21) )
          & m1_subset_1(X2,k1_zfmisc_1(sK21)) )
      & m1_subset_1(sK22,k1_zfmisc_1(sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f733,plain,
    ( ? [X2] :
        ( sK22 != k3_subset_1(sK21,X2)
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK22) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,sK22) ) )
            | ~ m1_subset_1(X3,sK21) )
        & m1_subset_1(X2,k1_zfmisc_1(sK21)) )
   => ( sK22 != k3_subset_1(sK21,sK23)
      & ! [X3] :
          ( ( ( ~ r2_hidden(X3,sK23)
              | ~ r2_hidden(X3,sK22) )
            & ( r2_hidden(X3,sK23)
              | r2_hidden(X3,sK22) ) )
          | ~ m1_subset_1(X3,sK21) )
      & m1_subset_1(sK23,k1_zfmisc_1(sK21)) ) ),
    introduced(choice_axiom,[])).

fof(f731,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f523])).

fof(f523,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f522])).

fof(f522,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f515])).

fof(f515,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ~ ( r2_hidden(X3,X1)
                    <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f514])).

fof(f514,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ~ ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_subset_1)).

fof(f2092,plain,(
    m1_subset_1(sK25(sK21,sK22,sK23),sK21) ),
    inference(unit_resulting_resolution,[],[f877,f878,f881,f896])).

fof(f896,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK25(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f745])).

fof(f745,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( sP1(X2,sK25(X0,X1,X2),X1)
            & m1_subset_1(sK25(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f697,f744])).

fof(f744,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP1(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP1(X2,sK25(X0,X1,X2),X1)
        & m1_subset_1(sK25(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f697,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( sP1(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f534,f696])).

fof(f696,plain,(
    ! [X2,X3,X1] :
      ( ( ~ r2_hidden(X3,X1)
      <~> r2_hidden(X3,X2) )
      | ~ sP1(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f534,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f533])).

fof(f533,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f513])).

fof(f513,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( ~ r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_subset_1)).

fof(f881,plain,(
    sK22 != k3_subset_1(sK21,sK23) ),
    inference(cnf_transformation,[],[f734])).

fof(f878,plain,(
    m1_subset_1(sK23,k1_zfmisc_1(sK21)) ),
    inference(cnf_transformation,[],[f734])).

fof(f877,plain,(
    m1_subset_1(sK22,k1_zfmisc_1(sK21)) ),
    inference(cnf_transformation,[],[f734])).

fof(f12029,plain,
    ( r2_hidden(sK25(sK21,sK22,sK23),sK23)
    | ~ r2_hidden(sK25(sK21,sK22,sK23),sK22) ),
    inference(resolution,[],[f2093,f894])).

fof(f894,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f743])).

fof(f743,plain,(
    ! [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X1,X0)
          | r2_hidden(X1,X2) )
        & ( r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f742])).

fof(f742,plain,(
    ! [X2,X3,X1] :
      ( ( ( ~ r2_hidden(X3,X2)
          | r2_hidden(X3,X1) )
        & ( r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) ) )
      | ~ sP1(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f696])).

fof(f2093,plain,(
    sP1(sK23,sK25(sK21,sK22,sK23),sK22) ),
    inference(unit_resulting_resolution,[],[f877,f878,f881,f897])).

fof(f897,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | sP1(X2,sK25(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f745])).

fof(f7202,plain,
    ( ~ r2_hidden(sK25(sK21,sK22,sK23),sK22)
    | ~ r2_hidden(sK25(sK21,sK22,sK23),sK23) ),
    inference(resolution,[],[f2092,f880])).

fof(f880,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK21)
      | ~ r2_hidden(X3,sK22)
      | ~ r2_hidden(X3,sK23) ) ),
    inference(cnf_transformation,[],[f734])).

fof(f12033,plain,(
    r2_hidden(sK25(sK21,sK22,sK23),sK22) ),
    inference(subsumption_resolution,[],[f12030,f12031])).

fof(f12030,plain,
    ( ~ r2_hidden(sK25(sK21,sK22,sK23),sK23)
    | r2_hidden(sK25(sK21,sK22,sK23),sK22) ),
    inference(resolution,[],[f2093,f895])).

fof(f895,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r2_hidden(X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f743])).
%------------------------------------------------------------------------------
