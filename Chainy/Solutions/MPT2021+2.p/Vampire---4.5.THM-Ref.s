%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2021+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 151 expanded)
%              Number of leaves         :    8 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  152 (1197 expanded)
%              Number of equality atoms :   40 ( 334 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5129,plain,(
    $false ),
    inference(global_subsumption,[],[f4765,f5128])).

fof(f5128,plain,(
    ~ r1_tarski(sK8,k7_setfam_1(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(forward_demodulation,[],[f5126,f4926])).

fof(f4926,plain,(
    u1_pre_topc(sK6) = u1_pre_topc(sK7) ),
    inference(unit_resulting_resolution,[],[f4552,f4712,f4589])).

fof(f4589,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f4425])).

fof(f4425,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f4712,plain,(
    m1_subset_1(u1_pre_topc(sK6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(unit_resulting_resolution,[],[f4548,f4680])).

fof(f4680,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4479])).

fof(f4479,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f4548,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f4493])).

fof(f4493,plain,
    ( ~ v2_tops_2(sK9,sK7)
    & v2_tops_2(sK8,sK6)
    & sK8 = sK9
    & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
    & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7))))
    & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6))))
    & l1_pre_topc(sK7)
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f4401,f4492,f4491,f4490,f4489])).

fof(f4489,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v2_tops_2(X3,X1)
                    & v2_tops_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,sK6)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f4490,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v2_tops_2(X3,X1)
                & v2_tops_2(X2,sK6)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6))
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
        & l1_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v2_tops_2(X3,sK7)
              & v2_tops_2(X2,sK6)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
      & l1_pre_topc(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f4491,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v2_tops_2(X3,sK7)
            & v2_tops_2(X2,sK6)
            & X2 = X3
            & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) )
   => ( ? [X3] :
          ( ~ v2_tops_2(X3,sK7)
          & v2_tops_2(sK8,sK6)
          & sK8 = X3
          & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
      & m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ) ),
    introduced(choice_axiom,[])).

fof(f4492,plain,
    ( ? [X3] :
        ( ~ v2_tops_2(X3,sK7)
        & v2_tops_2(sK8,sK6)
        & sK8 = X3
        & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) )
   => ( ~ v2_tops_2(sK9,sK7)
      & v2_tops_2(sK8,sK6)
      & sK8 = sK9
      & g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))
      & m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ) ),
    introduced(choice_axiom,[])).

fof(f4401,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f4400])).

fof(f4400,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v2_tops_2(X3,X1)
                  & v2_tops_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4387])).

fof(f4387,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( v2_tops_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v2_tops_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4386])).

fof(f4386,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( v2_tops_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tops_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_waybel_9)).

fof(f4552,plain,(
    g1_pre_topc(u1_struct_0(sK6),u1_pre_topc(sK6)) = g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) ),
    inference(cnf_transformation,[],[f4493])).

fof(f5126,plain,(
    ~ r1_tarski(sK8,k7_setfam_1(u1_struct_0(sK6),u1_pre_topc(sK7))) ),
    inference(superposition,[],[f4799,f4925])).

fof(f4925,plain,(
    u1_struct_0(sK6) = u1_struct_0(sK7) ),
    inference(unit_resulting_resolution,[],[f4552,f4712,f4588])).

fof(f4588,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f4425])).

fof(f4799,plain,(
    ~ r1_tarski(sK8,k7_setfam_1(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    inference(unit_resulting_resolution,[],[f4549,f4710,f4711,f4583])).

fof(f4583,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f4505])).

fof(f4505,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_2(X1,X0)
              | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
            & ( r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
              | ~ v2_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f4421])).

fof(f4421,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2433])).

fof(f2433,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f4711,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(forward_demodulation,[],[f4551,f4553])).

fof(f4553,plain,(
    sK8 = sK9 ),
    inference(cnf_transformation,[],[f4493])).

fof(f4551,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK7)))) ),
    inference(cnf_transformation,[],[f4493])).

fof(f4710,plain,(
    ~ v2_tops_2(sK8,sK7) ),
    inference(forward_demodulation,[],[f4555,f4553])).

fof(f4555,plain,(
    ~ v2_tops_2(sK9,sK7) ),
    inference(cnf_transformation,[],[f4493])).

fof(f4549,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f4493])).

fof(f4765,plain,(
    r1_tarski(sK8,k7_setfam_1(u1_struct_0(sK6),u1_pre_topc(sK6))) ),
    inference(unit_resulting_resolution,[],[f4548,f4554,f4550,f4582])).

fof(f4582,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f4505])).

fof(f4550,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK6)))) ),
    inference(cnf_transformation,[],[f4493])).

fof(f4554,plain,(
    v2_tops_2(sK8,sK6) ),
    inference(cnf_transformation,[],[f4493])).
%------------------------------------------------------------------------------
