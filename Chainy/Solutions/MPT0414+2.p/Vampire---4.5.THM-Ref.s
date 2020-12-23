%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0414+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:29 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 148 expanded)
%              Number of leaves         :    8 (  45 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 831 expanded)
%              Number of equality atoms :   18 ( 114 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1086,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1080,f1085])).

fof(f1085,plain,(
    r2_hidden(sK6(sK1,sK2),sK2) ),
    inference(subsumption_resolution,[],[f1079,f713])).

fof(f713,plain,(
    ~ sQ14_eqProxy(sK1,sK2) ),
    inference(equality_proxy_replacement,[],[f664,f712])).

fof(f712,plain,(
    ! [X1,X0] :
      ( sQ14_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ14_eqProxy])])).

fof(f664,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f626])).

fof(f626,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f623,f625,f624])).

fof(f624,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f625,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f623,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f600])).

fof(f600,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f599])).

fof(f599,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f590])).

fof(f590,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f589])).

fof(f589,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_setfam_1)).

fof(f1079,plain,
    ( sQ14_eqProxy(sK1,sK2)
    | r2_hidden(sK6(sK1,sK2),sK2) ),
    inference(resolution,[],[f1030,f718])).

fof(f718,plain,(
    ! [X0,X1] :
      ( sQ14_eqProxy(X0,X1)
      | r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f676,f712])).

fof(f676,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK6(X0,X1),X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f640])).

fof(f640,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f638,f639])).

fof(f639,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f638,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f603])).

fof(f603,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f1030,plain,(
    ~ r2_hidden(sK6(sK1,sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f1025])).

fof(f1025,plain,
    ( ~ r2_hidden(sK6(sK1,sK2),sK1)
    | ~ r2_hidden(sK6(sK1,sK2),sK1) ),
    inference(resolution,[],[f731,f794])).

fof(f794,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f785,f750])).

fof(f750,plain,(
    ! [X11] :
      ( r2_hidden(X11,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X11,sK1) ) ),
    inference(resolution,[],[f660,f690])).

fof(f690,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f613])).

fof(f613,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f660,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f626])).

fof(f785,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f662,f696])).

fof(f696,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f619])).

fof(f619,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f568])).

fof(f568,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f662,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f626])).

fof(f731,plain,
    ( ~ r2_hidden(sK6(sK1,sK2),sK2)
    | ~ r2_hidden(sK6(sK1,sK2),sK1) ),
    inference(resolution,[],[f713,f717])).

fof(f717,plain,(
    ! [X0,X1] :
      ( sQ14_eqProxy(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1)
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f677,f712])).

fof(f677,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK6(X0,X1),X1)
      | ~ r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f640])).

fof(f1080,plain,(
    ~ r2_hidden(sK6(sK1,sK2),sK2) ),
    inference(resolution,[],[f1030,f809])).

fof(f809,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(subsumption_resolution,[],[f800,f771])).

fof(f771,plain,(
    ! [X11] :
      ( r2_hidden(X11,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X11,sK2) ) ),
    inference(resolution,[],[f661,f690])).

fof(f661,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f626])).

fof(f800,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,sK1)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f663,f696])).

fof(f663,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f626])).
%------------------------------------------------------------------------------
