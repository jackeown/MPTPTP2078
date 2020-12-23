%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1381+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:20 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 107 expanded)
%              Number of leaves         :    8 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  177 ( 683 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6190,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6189,f3627])).

fof(f3627,plain,(
    ~ r2_hidden(sK87,sK86) ),
    inference(cnf_transformation,[],[f3207])).

fof(f3207,plain,
    ( ~ r2_hidden(sK87,sK86)
    & m1_connsp_2(sK86,sK85,sK87)
    & m1_subset_1(sK87,u1_struct_0(sK85))
    & m1_subset_1(sK86,k1_zfmisc_1(u1_struct_0(sK85)))
    & l1_pre_topc(sK85)
    & v2_pre_topc(sK85)
    & ~ v2_struct_0(sK85) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK85,sK86,sK87])],[f2535,f3206,f3205,f3204])).

fof(f3204,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(X2,X1)
                & m1_connsp_2(X1,X0,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,sK85,X2)
              & m1_subset_1(X2,u1_struct_0(sK85)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK85))) )
      & l1_pre_topc(sK85)
      & v2_pre_topc(sK85)
      & ~ v2_struct_0(sK85) ) ),
    introduced(choice_axiom,[])).

fof(f3205,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & m1_connsp_2(X1,sK85,X2)
            & m1_subset_1(X2,u1_struct_0(sK85)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK85))) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK86)
          & m1_connsp_2(sK86,sK85,X2)
          & m1_subset_1(X2,u1_struct_0(sK85)) )
      & m1_subset_1(sK86,k1_zfmisc_1(u1_struct_0(sK85))) ) ),
    introduced(choice_axiom,[])).

fof(f3206,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,sK86)
        & m1_connsp_2(sK86,sK85,X2)
        & m1_subset_1(X2,u1_struct_0(sK85)) )
   => ( ~ r2_hidden(sK87,sK86)
      & m1_connsp_2(sK86,sK85,sK87)
      & m1_subset_1(sK87,u1_struct_0(sK85)) ) ),
    introduced(choice_axiom,[])).

fof(f2535,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f2534])).

fof(f2534,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(X2,X1)
              & m1_connsp_2(X1,X0,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2522])).

fof(f2522,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( m1_connsp_2(X1,X0,X2)
                 => r2_hidden(X2,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f2521])).

fof(f2521,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f6189,plain,(
    r2_hidden(sK87,sK86) ),
    inference(subsumption_resolution,[],[f6187,f3625])).

fof(f3625,plain,(
    m1_subset_1(sK87,u1_struct_0(sK85)) ),
    inference(cnf_transformation,[],[f3207])).

fof(f6187,plain,
    ( ~ m1_subset_1(sK87,u1_struct_0(sK85))
    | r2_hidden(sK87,sK86) ),
    inference(resolution,[],[f5109,f3626])).

fof(f3626,plain,(
    m1_connsp_2(sK86,sK85,sK87) ),
    inference(cnf_transformation,[],[f3207])).

fof(f5109,plain,(
    ! [X0] :
      ( ~ m1_connsp_2(sK86,sK85,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK85))
      | r2_hidden(X0,sK86) ) ),
    inference(resolution,[],[f4607,f4650])).

fof(f4650,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_tops_1(sK85,sK86))
      | r2_hidden(X0,sK86) ) ),
    inference(resolution,[],[f4624,f3642])).

fof(f3642,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3218])).

fof(f3218,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK90(X0,X1),X1)
          & r2_hidden(sK90(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK90])],[f3216,f3217])).

fof(f3217,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK90(X0,X1),X1)
        & r2_hidden(sK90(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f3216,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f3215])).

fof(f3215,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2544])).

fof(f2544,plain,(
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

fof(f4624,plain,(
    r1_tarski(k1_tops_1(sK85,sK86),sK86) ),
    inference(subsumption_resolution,[],[f4578,f3623])).

fof(f3623,plain,(
    l1_pre_topc(sK85) ),
    inference(cnf_transformation,[],[f3207])).

fof(f4578,plain,
    ( r1_tarski(k1_tops_1(sK85,sK86),sK86)
    | ~ l1_pre_topc(sK85) ),
    inference(resolution,[],[f3624,f3873])).

fof(f3873,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2711])).

fof(f2711,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2159])).

fof(f2159,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f3624,plain,(
    m1_subset_1(sK86,k1_zfmisc_1(u1_struct_0(sK85))) ),
    inference(cnf_transformation,[],[f3207])).

fof(f4607,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_tops_1(sK85,sK86))
      | ~ m1_connsp_2(sK86,sK85,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK85)) ) ),
    inference(subsumption_resolution,[],[f4606,f3621])).

fof(f3621,plain,(
    ~ v2_struct_0(sK85) ),
    inference(cnf_transformation,[],[f3207])).

fof(f4606,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK86,sK85,X1)
      | r2_hidden(X1,k1_tops_1(sK85,sK86))
      | ~ m1_subset_1(X1,u1_struct_0(sK85))
      | v2_struct_0(sK85) ) ),
    inference(subsumption_resolution,[],[f4605,f3622])).

fof(f3622,plain,(
    v2_pre_topc(sK85) ),
    inference(cnf_transformation,[],[f3207])).

fof(f4605,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK86,sK85,X1)
      | r2_hidden(X1,k1_tops_1(sK85,sK86))
      | ~ m1_subset_1(X1,u1_struct_0(sK85))
      | ~ v2_pre_topc(sK85)
      | v2_struct_0(sK85) ) ),
    inference(subsumption_resolution,[],[f4563,f3623])).

fof(f4563,plain,(
    ! [X1] :
      ( ~ m1_connsp_2(sK86,sK85,X1)
      | r2_hidden(X1,k1_tops_1(sK85,sK86))
      | ~ m1_subset_1(X1,u1_struct_0(sK85))
      | ~ l1_pre_topc(sK85)
      | ~ v2_pre_topc(sK85)
      | v2_struct_0(sK85) ) ),
    inference(resolution,[],[f3624,f3677])).

fof(f3677,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3245])).

fof(f3245,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2570])).

fof(f2570,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2569])).

fof(f2569,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2514])).

fof(f2514,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).
%------------------------------------------------------------------------------
