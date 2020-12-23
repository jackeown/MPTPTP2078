%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT2004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:39 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   16 (  43 expanded)
%              Number of leaves         :    5 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 375 expanded)
%              Number of equality atoms :   28 ( 106 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5490,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5317,f5243])).

fof(f5243,plain,(
    m1_setfam_1(sK16,u1_struct_0(sK13)) ),
    inference(definition_unfolding,[],[f4825,f4824])).

fof(f4824,plain,(
    sK15 = sK16 ),
    inference(cnf_transformation,[],[f4540])).

fof(f4540,plain,
    ( ~ m1_setfam_1(sK16,u1_struct_0(sK14))
    & m1_setfam_1(sK15,u1_struct_0(sK13))
    & sK15 = sK16
    & u1_struct_0(sK13) = u1_struct_0(sK14)
    & m1_subset_1(sK16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14))))
    & m1_subset_1(sK15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13))))
    & l1_struct_0(sK14)
    & l1_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f4333,f4539,f4538,f4537,f4536])).

fof(f4536,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_setfam_1(X3,u1_struct_0(X1))
                    & m1_setfam_1(X2,u1_struct_0(X0))
                    & X2 = X3
                    & u1_struct_0(X0) = u1_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_setfam_1(X3,u1_struct_0(X1))
                  & m1_setfam_1(X2,u1_struct_0(sK13))
                  & X2 = X3
                  & u1_struct_0(X1) = u1_struct_0(sK13)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK13) ) ),
    introduced(choice_axiom,[])).

fof(f4537,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_setfam_1(X3,u1_struct_0(X1))
                & m1_setfam_1(X2,u1_struct_0(sK13))
                & X2 = X3
                & u1_struct_0(X1) = u1_struct_0(sK13)
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_setfam_1(X3,u1_struct_0(sK14))
              & m1_setfam_1(X2,u1_struct_0(sK13))
              & X2 = X3
              & u1_struct_0(sK13) = u1_struct_0(sK14)
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) )
      & l1_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f4538,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_setfam_1(X3,u1_struct_0(sK14))
            & m1_setfam_1(X2,u1_struct_0(sK13))
            & X2 = X3
            & u1_struct_0(sK13) = u1_struct_0(sK14)
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) )
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) )
   => ( ? [X3] :
          ( ~ m1_setfam_1(X3,u1_struct_0(sK14))
          & m1_setfam_1(sK15,u1_struct_0(sK13))
          & sK15 = X3
          & u1_struct_0(sK13) = u1_struct_0(sK14)
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) )
      & m1_subset_1(sK15,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK13)))) ) ),
    introduced(choice_axiom,[])).

fof(f4539,plain,
    ( ? [X3] :
        ( ~ m1_setfam_1(X3,u1_struct_0(sK14))
        & m1_setfam_1(sK15,u1_struct_0(sK13))
        & sK15 = X3
        & u1_struct_0(sK13) = u1_struct_0(sK14)
        & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) )
   => ( ~ m1_setfam_1(sK16,u1_struct_0(sK14))
      & m1_setfam_1(sK15,u1_struct_0(sK13))
      & sK15 = sK16
      & u1_struct_0(sK13) = u1_struct_0(sK14)
      & m1_subset_1(sK16,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK14)))) ) ),
    introduced(choice_axiom,[])).

fof(f4333,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_setfam_1(X3,u1_struct_0(X1))
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & X2 = X3
                  & u1_struct_0(X0) = u1_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f4332])).

fof(f4332,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_setfam_1(X3,u1_struct_0(X1))
                  & m1_setfam_1(X2,u1_struct_0(X0))
                  & X2 = X3
                  & u1_struct_0(X0) = u1_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4313])).

fof(f4313,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                   => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                        & X2 = X3
                        & u1_struct_0(X0) = u1_struct_0(X1) )
                     => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4312])).

fof(f4312,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
                 => ( ( m1_setfam_1(X2,u1_struct_0(X0))
                      & X2 = X3
                      & u1_struct_0(X0) = u1_struct_0(X1) )
                   => m1_setfam_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_waybel_9)).

fof(f4825,plain,(
    m1_setfam_1(sK15,u1_struct_0(sK13)) ),
    inference(cnf_transformation,[],[f4540])).

fof(f5317,plain,(
    ~ m1_setfam_1(sK16,u1_struct_0(sK13)) ),
    inference(backward_demodulation,[],[f4826,f4823])).

fof(f4823,plain,(
    u1_struct_0(sK13) = u1_struct_0(sK14) ),
    inference(cnf_transformation,[],[f4540])).

fof(f4826,plain,(
    ~ m1_setfam_1(sK16,u1_struct_0(sK14)) ),
    inference(cnf_transformation,[],[f4540])).
%------------------------------------------------------------------------------
