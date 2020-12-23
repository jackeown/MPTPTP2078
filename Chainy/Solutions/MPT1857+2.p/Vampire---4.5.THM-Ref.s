%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1857+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:35 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   65 (1138 expanded)
%              Number of leaves         :   11 ( 501 expanded)
%              Depth                    :   14
%              Number of atoms          :  295 (9736 expanded)
%              Number of equality atoms :   58 (2576 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5439,plain,(
    $false ),
    inference(global_subsumption,[],[f4198,f4247,f5438])).

fof(f5438,plain,
    ( ~ r2_hidden(sK9(sK4,sK6,sK8(sK5,sK6)),u1_pre_topc(sK4))
    | ~ m1_subset_1(sK9(sK4,sK6,sK8(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(forward_demodulation,[],[f5437,f3987])).

fof(f3987,plain,(
    u1_pre_topc(sK4) = u1_pre_topc(sK5) ),
    inference(unit_resulting_resolution,[],[f3773,f3905,f3786])).

fof(f3786,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3663])).

fof(f3663,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1808])).

fof(f1808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f3905,plain,(
    m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(unit_resulting_resolution,[],[f3769,f3874])).

fof(f3874,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3711])).

fof(f3711,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3769,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3722])).

fof(f3722,plain,
    ( ~ v2_tex_2(sK7,sK5)
    & v2_tex_2(sK6,sK4)
    & sK6 = sK7
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5)))
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4)))
    & l1_pre_topc(sK5)
    & l1_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f3658,f3721,f3720,f3719,f3718])).

fof(f3718,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tex_2(X3,X1)
                    & v2_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,sK4)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3719,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tex_2(X3,X1)
                & v2_tex_2(X2,sK4)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tex_2(X3,sK5)
              & v2_tex_2(X2,sK4)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
      & l1_pre_topc(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3720,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tex_2(X3,sK5)
            & v2_tex_2(X2,sK4)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4))) )
   => ( ? [X3] :
          ( ~ v2_tex_2(X3,sK5)
          & v2_tex_2(sK6,sK4)
          & sK6 = X3
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    introduced(choice_axiom,[])).

fof(f3721,plain,
    ( ? [X3] :
        ( ~ v2_tex_2(X3,sK5)
        & v2_tex_2(sK6,sK4)
        & sK6 = X3
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ~ v2_tex_2(sK7,sK5)
      & v2_tex_2(sK6,sK4)
      & sK6 = sK7
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5))
      & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f3658,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3657])).

fof(f3657,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tex_2(X3,X1)
                  & v2_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3648])).

fof(f3648,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3647])).

fof(f3647,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tex_2)).

fof(f3773,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) ),
    inference(cnf_transformation,[],[f3722])).

fof(f5437,plain,
    ( ~ m1_subset_1(sK9(sK4,sK6,sK8(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK9(sK4,sK6,sK8(sK5,sK6)),u1_pre_topc(sK5)) ),
    inference(forward_demodulation,[],[f5434,f3986])).

fof(f3986,plain,(
    u1_struct_0(sK4) = u1_struct_0(sK5) ),
    inference(unit_resulting_resolution,[],[f3773,f3905,f3785])).

fof(f3785,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f3663])).

fof(f5434,plain,
    ( ~ m1_subset_1(sK9(sK4,sK6,sK8(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(sK9(sK4,sK6,sK8(sK5,sK6)),u1_pre_topc(sK5)) ),
    inference(resolution,[],[f5429,f3924])).

fof(f3924,plain,(
    ! [X10] :
      ( v3_pre_topc(X10,sK5)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ r2_hidden(X10,u1_pre_topc(sK5)) ) ),
    inference(resolution,[],[f3770,f3873])).

fof(f3873,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f3764])).

fof(f3764,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3710])).

fof(f3710,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1774])).

fof(f1774,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f3770,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f3722])).

fof(f5429,plain,(
    ~ v3_pre_topc(sK9(sK4,sK6,sK8(sK5,sK6)),sK5) ),
    inference(unit_resulting_resolution,[],[f3903,f3771,f4198,f4200,f4025])).

fof(f4025,plain,(
    ! [X4,X3] :
      ( sK8(sK5,X3) != k9_subset_1(u1_struct_0(sK4),X3,X4)
      | v2_tex_2(X3,sK5)
      | ~ v3_pre_topc(X4,sK5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4))) ) ),
    inference(global_subsumption,[],[f3770,f3999])).

fof(f3999,plain,(
    ! [X4,X3] :
      ( sK8(sK5,X3) != k9_subset_1(u1_struct_0(sK4),X3,X4)
      | v2_tex_2(X3,sK5)
      | ~ v3_pre_topc(X4,sK5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK4)))
      | ~ l1_pre_topc(sK5) ) ),
    inference(superposition,[],[f3782,f3986])).

fof(f3782,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK8(X0,X1)
      | v2_tex_2(X1,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3727])).

fof(f3727,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK8(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK8(X0,X1),X1)
                & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK9(X0,X1,X4)) = X4
                    & v3_pre_topc(sK9(X0,X1,X4),X0)
                    & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f3724,f3726,f3725])).

fof(f3725,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK8(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK8(X0,X1),X1)
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3726,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK9(X0,X1,X4)) = X4
        & v3_pre_topc(sK9(X0,X1,X4),X0)
        & m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f3724,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f3723])).

fof(f3723,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3660])).

fof(f3660,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3659])).

fof(f3659,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3595])).

fof(f3595,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tex_2)).

fof(f4200,plain,(
    sK8(sK5,sK6) = k9_subset_1(u1_struct_0(sK4),sK6,sK9(sK4,sK6,sK8(sK5,sK6))) ),
    inference(unit_resulting_resolution,[],[f3769,f3775,f3929,f3771,f4052,f3779])).

fof(f3779,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),X1,sK9(X0,X1,X4)) = X4 ) ),
    inference(cnf_transformation,[],[f3727])).

fof(f4052,plain,(
    m1_subset_1(sK8(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(superposition,[],[f3928,f3986])).

fof(f3928,plain,(
    m1_subset_1(sK8(sK5,sK6),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(unit_resulting_resolution,[],[f3770,f3903,f3904,f3780])).

fof(f3780,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3727])).

fof(f3904,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(forward_demodulation,[],[f3772,f3774])).

fof(f3774,plain,(
    sK6 = sK7 ),
    inference(cnf_transformation,[],[f3722])).

fof(f3772,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f3722])).

fof(f3929,plain,(
    r1_tarski(sK8(sK5,sK6),sK6) ),
    inference(unit_resulting_resolution,[],[f3770,f3903,f3904,f3781])).

fof(f3781,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(sK8(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f3727])).

fof(f3775,plain,(
    v2_tex_2(sK6,sK4) ),
    inference(cnf_transformation,[],[f3722])).

fof(f3771,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f3722])).

fof(f3903,plain,(
    ~ v2_tex_2(sK6,sK5) ),
    inference(forward_demodulation,[],[f3776,f3774])).

fof(f3776,plain,(
    ~ v2_tex_2(sK7,sK5) ),
    inference(cnf_transformation,[],[f3722])).

fof(f4247,plain,(
    r2_hidden(sK9(sK4,sK6,sK8(sK5,sK6)),u1_pre_topc(sK4)) ),
    inference(global_subsumption,[],[f4198,f4242])).

fof(f4242,plain,
    ( ~ m1_subset_1(sK9(sK4,sK6,sK8(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4)))
    | r2_hidden(sK9(sK4,sK6,sK8(sK5,sK6)),u1_pre_topc(sK4)) ),
    inference(resolution,[],[f3913,f4199])).

fof(f4199,plain,(
    v3_pre_topc(sK9(sK4,sK6,sK8(sK5,sK6)),sK4) ),
    inference(unit_resulting_resolution,[],[f3769,f3775,f3929,f3771,f4052,f3778])).

fof(f3778,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(sK9(X0,X1,X4),X0) ) ),
    inference(cnf_transformation,[],[f3727])).

fof(f3913,plain,(
    ! [X9] :
      ( ~ v3_pre_topc(X9,sK4)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK4)))
      | r2_hidden(X9,u1_pre_topc(sK4)) ) ),
    inference(resolution,[],[f3769,f3872])).

fof(f3872,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f3764])).

fof(f4198,plain,(
    m1_subset_1(sK9(sK4,sK6,sK8(sK5,sK6)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unit_resulting_resolution,[],[f3769,f3775,f3771,f3929,f4052,f3777])).

fof(f3777,plain,(
    ! [X4,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3727])).
%------------------------------------------------------------------------------
