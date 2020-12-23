%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0371+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:26 EST 2020

% Result     : Theorem 5.49s
% Output     : Refutation 5.49s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 266 expanded)
%              Number of leaves         :    6 (  84 expanded)
%              Depth                    :   12
%              Number of atoms          :  152 (1802 expanded)
%              Number of equality atoms :   18 ( 252 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10564,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10563,f10561])).

fof(f10561,plain,(
    r2_hidden(sK23(sK20,sK21,sK22),sK21) ),
    inference(subsumption_resolution,[],[f10559,f7156])).

fof(f7156,plain,
    ( r2_hidden(sK23(sK20,sK21,sK22),sK21)
    | r2_hidden(sK23(sK20,sK21,sK22),sK22) ),
    inference(resolution,[],[f2071,f870])).

fof(f870,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK20)
      | r2_hidden(X3,sK21)
      | r2_hidden(X3,sK22) ) ),
    inference(cnf_transformation,[],[f729])).

fof(f729,plain,
    ( sK21 != k3_subset_1(sK20,sK22)
    & ! [X3] :
        ( ( ( ~ r2_hidden(X3,sK21)
            | ~ r2_hidden(X3,sK22) )
          & ( r2_hidden(X3,sK22)
            | r2_hidden(X3,sK21) ) )
        | ~ m1_subset_1(X3,sK20) )
    & m1_subset_1(sK22,k1_zfmisc_1(sK20))
    & m1_subset_1(sK21,k1_zfmisc_1(sK20)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20,sK21,sK22])],[f726,f728,f727])).

fof(f727,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k3_subset_1(X0,X2) != X1
            & ! [X3] :
                ( ( ( ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK21 != k3_subset_1(sK20,X2)
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,sK21)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,sK21) ) )
              | ~ m1_subset_1(X3,sK20) )
          & m1_subset_1(X2,k1_zfmisc_1(sK20)) )
      & m1_subset_1(sK21,k1_zfmisc_1(sK20)) ) ),
    introduced(choice_axiom,[])).

fof(f728,plain,
    ( ? [X2] :
        ( sK21 != k3_subset_1(sK20,X2)
        & ! [X3] :
            ( ( ( ~ r2_hidden(X3,sK21)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,sK21) ) )
            | ~ m1_subset_1(X3,sK20) )
        & m1_subset_1(X2,k1_zfmisc_1(sK20)) )
   => ( sK21 != k3_subset_1(sK20,sK22)
      & ! [X3] :
          ( ( ( ~ r2_hidden(X3,sK21)
              | ~ r2_hidden(X3,sK22) )
            & ( r2_hidden(X3,sK22)
              | r2_hidden(X3,sK21) ) )
          | ~ m1_subset_1(X3,sK20) )
      & m1_subset_1(sK22,k1_zfmisc_1(sK20)) ) ),
    introduced(choice_axiom,[])).

fof(f726,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ( ~ r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f522])).

fof(f522,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f521])).

fof(f521,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k3_subset_1(X0,X2) != X1
          & ! [X3] :
              ( ( ~ r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f514])).

fof(f514,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( ~ r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => k3_subset_1(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f513])).

fof(f513,conjecture,(
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

fof(f2071,plain,(
    m1_subset_1(sK23(sK20,sK21,sK22),sK20) ),
    inference(unit_resulting_resolution,[],[f868,f869,f872,f883])).

fof(f883,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | m1_subset_1(sK23(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f736])).

fof(f736,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ( sP0(X2,sK23(X0,X1,X2),X1)
            & m1_subset_1(sK23(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f692,f735])).

fof(f735,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP0(X2,X3,X1)
          & m1_subset_1(X3,X0) )
     => ( sP0(X2,sK23(X0,X1,X2),X1)
        & m1_subset_1(sK23(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f692,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( sP0(X2,X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_folding,[],[f531,f691])).

fof(f691,plain,(
    ! [X2,X3,X1] :
      ( ( r2_hidden(X3,X1)
      <~> ~ r2_hidden(X3,X2) )
      | ~ sP0(X2,X3,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f531,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f530])).

fof(f530,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,X2) = X1
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> ~ r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f512])).

fof(f512,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> ~ r2_hidden(X3,X2) ) )
           => k3_subset_1(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_subset_1)).

fof(f872,plain,(
    sK21 != k3_subset_1(sK20,sK22) ),
    inference(cnf_transformation,[],[f729])).

fof(f869,plain,(
    m1_subset_1(sK22,k1_zfmisc_1(sK20)) ),
    inference(cnf_transformation,[],[f729])).

fof(f868,plain,(
    m1_subset_1(sK21,k1_zfmisc_1(sK20)) ),
    inference(cnf_transformation,[],[f729])).

fof(f10559,plain,
    ( ~ r2_hidden(sK23(sK20,sK21,sK22),sK22)
    | r2_hidden(sK23(sK20,sK21,sK22),sK21) ),
    inference(resolution,[],[f2072,f881])).

fof(f881,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r2_hidden(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f734])).

fof(f734,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X1,X0)
          | ~ r2_hidden(X1,X2) )
        & ( ~ r2_hidden(X1,X0)
          | r2_hidden(X1,X2) ) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f733])).

fof(f733,plain,(
    ! [X2,X3,X1] :
      ( ( ( r2_hidden(X3,X2)
          | ~ r2_hidden(X3,X1) )
        & ( ~ r2_hidden(X3,X2)
          | r2_hidden(X3,X1) ) )
      | ~ sP0(X2,X3,X1) ) ),
    inference(nnf_transformation,[],[f691])).

fof(f2072,plain,(
    sP0(sK22,sK23(sK20,sK21,sK22),sK21) ),
    inference(unit_resulting_resolution,[],[f868,f869,f872,f884])).

fof(f884,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,X2) = X1
      | sP0(X2,sK23(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f736])).

fof(f10563,plain,(
    ~ r2_hidden(sK23(sK20,sK21,sK22),sK21) ),
    inference(subsumption_resolution,[],[f10560,f10562])).

fof(f10562,plain,(
    ~ r2_hidden(sK23(sK20,sK21,sK22),sK22) ),
    inference(subsumption_resolution,[],[f7155,f10561])).

fof(f7155,plain,
    ( ~ r2_hidden(sK23(sK20,sK21,sK22),sK22)
    | ~ r2_hidden(sK23(sK20,sK21,sK22),sK21) ),
    inference(resolution,[],[f2071,f871])).

fof(f871,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK20)
      | ~ r2_hidden(X3,sK22)
      | ~ r2_hidden(X3,sK21) ) ),
    inference(cnf_transformation,[],[f729])).

fof(f10560,plain,
    ( r2_hidden(sK23(sK20,sK21,sK22),sK22)
    | ~ r2_hidden(sK23(sK20,sK21,sK22),sK21) ),
    inference(resolution,[],[f2072,f882])).

fof(f882,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ r2_hidden(X1,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f734])).
%------------------------------------------------------------------------------
