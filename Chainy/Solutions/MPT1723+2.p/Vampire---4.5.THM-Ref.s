%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1723+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 2.01s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 481 expanded)
%              Number of leaves         :    8 ( 209 expanded)
%              Depth                    :   35
%              Number of atoms          :  559 (6668 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3940,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3939,f3537])).

fof(f3537,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f3535,f3452])).

fof(f3452,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3429,plain,
    ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
        & m1_pre_topc(sK2,sK3) )
      | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3383,f3428,f3427,f3426,f3425])).

fof(f3425,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                        & m1_pre_topc(X2,X3) )
                      | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3426,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X1,X3))
                    & m1_pre_topc(X2,X3) )
                  | ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X2))
                    & m1_pre_topc(X1,X3) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3))
                  & m1_pre_topc(X2,X3) )
                | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2))
                  & m1_pre_topc(sK1,X3) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3427,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,sK1,X3))
                & m1_pre_topc(X2,X3) )
              | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X2))
                & m1_pre_topc(sK1,X3) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3))
              & m1_pre_topc(sK2,X3) )
            | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2))
              & m1_pre_topc(sK1,X3) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3428,plain,
    ( ? [X3] :
        ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,X3))
            & m1_pre_topc(sK2,X3) )
          | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,sK2))
            & m1_pre_topc(sK1,X3) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
          & m1_pre_topc(sK2,sK3) )
        | ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
          & m1_pre_topc(sK1,sK3) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3383,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3382])).

fof(f3382,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      & m1_pre_topc(X2,X3) )
                    | ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3371])).

fof(f3371,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                        & ( m1_pre_topc(X1,X3)
                         => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3370])).

fof(f3370,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tmap_1)).

fof(f3535,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f3521,f3450])).

fof(f3450,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3521,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3422])).

fof(f3422,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f3939,plain,(
    ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f3938,f3522])).

fof(f3522,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3423])).

fof(f3423,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3366])).

fof(f3366,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f3938,plain,(
    ~ m1_pre_topc(sK1,sK1) ),
    inference(subsumption_resolution,[],[f3937,f3448])).

fof(f3448,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3937,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3936,f3449])).

fof(f3449,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3936,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3935,f3450])).

fof(f3935,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3934,f3453])).

fof(f3453,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3934,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3933,f3454])).

fof(f3454,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3933,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3932,f3451])).

fof(f3451,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3932,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3931,f3452])).

fof(f3931,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3930,f3455])).

fof(f3455,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3930,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3929,f3456])).

fof(f3456,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3929,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3928,f3805])).

fof(f3805,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3804,f3538])).

fof(f3538,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f3535,f3454])).

fof(f3804,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3792,f3522])).

fof(f3792,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3791,f3458])).

fof(f3458,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3791,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3790,f3448])).

fof(f3790,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3789,f3449])).

fof(f3789,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3788,f3450])).

fof(f3788,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3787,f3451])).

fof(f3787,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3786,f3452])).

fof(f3786,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3785,f3455])).

fof(f3785,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3784,f3456])).

fof(f3784,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3783,f3453])).

fof(f3783,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3782,f3454])).

fof(f3782,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(subsumption_resolution,[],[f3769,f3457])).

fof(f3457,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3769,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f3766])).

fof(f3766,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2,sK3) ),
    inference(resolution,[],[f3465,f3459])).

fof(f3459,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3465,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X4)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f3928,plain,
    ( ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3927,f3457])).

fof(f3927,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3926])).

fof(f3926,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK1,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f3815,f3465])).

fof(f3815,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3814,f3538])).

fof(f3814,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ l1_pre_topc(sK2) ),
    inference(resolution,[],[f3781,f3522])).

fof(f3781,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3780,f3460])).

fof(f3460,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f3429])).

fof(f3780,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3779,f3448])).

fof(f3779,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3778,f3449])).

fof(f3778,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3777,f3450])).

fof(f3777,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3776,f3451])).

fof(f3776,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3775,f3452])).

fof(f3775,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3774,f3455])).

fof(f3774,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3773,f3456])).

fof(f3773,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3772,f3453])).

fof(f3772,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3771,f3454])).

fof(f3771,plain,
    ( ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f3770,f3457])).

fof(f3770,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(duplicate_literal_removal,[],[f3765])).

fof(f3765,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(resolution,[],[f3465,f3461])).

fof(f3461,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f3429])).
%------------------------------------------------------------------------------
