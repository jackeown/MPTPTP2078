%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1324+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:18 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   26 (  58 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 287 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3062,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3061,f2475])).

fof(f2475,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f2436])).

fof(f2436,plain,
    ( ~ r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),sK5))
    & r1_tarski(sK4,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,sK5)))
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f2396,f2435,f2434,f2433])).

fof(f2433,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
                & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK3),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,X1)),k1_tops_2(sK3,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2434,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(sK3),X2))
            & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,X1)),k1_tops_2(sK3,X1,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),X2))
          & r1_tarski(sK4,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
      & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f2435,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),X2))
        & r1_tarski(sK4,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
   => ( ~ r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),sK5))
      & r1_tarski(sK4,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,sK5)))
      & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ) ),
    introduced(choice_axiom,[])).

fof(f2396,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2395])).

fof(f2395,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2))
              & r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2385])).

fof(f2385,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
                 => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f2384])).

fof(f2384,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)))
               => r1_tarski(X1,k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_tops_2)).

fof(f3061,plain,(
    ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f3060,f2476])).

fof(f2476,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f2436])).

fof(f3060,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f3059,f2477])).

fof(f2477,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f2436])).

fof(f3059,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f3044,f2479])).

fof(f2479,plain,(
    ~ r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),sK5)) ),
    inference(cnf_transformation,[],[f2436])).

fof(f3044,plain,
    ( r1_tarski(sK4,k5_setfam_1(u1_struct_0(sK3),sK5))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3) ),
    inference(resolution,[],[f2657,f2529])).

fof(f2529,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2417])).

fof(f2417,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2383])).

fof(f2383,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(X0,X1)),k1_tops_2(X0,X1,X2)),k5_setfam_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_2)).

fof(f2657,plain,(
    ! [X2] :
      ( ~ r1_tarski(k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,sK5)),X2)
      | r1_tarski(sK4,X2) ) ),
    inference(resolution,[],[f2478,f2480])).

fof(f2480,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2398])).

fof(f2398,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2397])).

fof(f2397,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2478,plain,(
    r1_tarski(sK4,k5_setfam_1(u1_struct_0(k1_pre_topc(sK3,sK4)),k1_tops_2(sK3,sK4,sK5))) ),
    inference(cnf_transformation,[],[f2436])).
%------------------------------------------------------------------------------
