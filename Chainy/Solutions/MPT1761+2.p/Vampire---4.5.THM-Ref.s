%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1761+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 7.67s
% Output     : Refutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 359 expanded)
%              Number of leaves         :   17 ( 193 expanded)
%              Depth                    :   12
%              Number of atoms          :  385 (5574 expanded)
%              Number of equality atoms :   40 ( 465 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16538,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16511,f6705])).

fof(f6705,plain,(
    m1_subset_1(u1_struct_0(sK98),k1_zfmisc_1(u1_struct_0(sK99))) ),
    inference(unit_resulting_resolution,[],[f4650,f6567,f4822])).

fof(f4822,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3531])).

fof(f3531,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3362])).

fof(f3362,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f6567,plain,(
    l1_pre_topc(sK99) ),
    inference(unit_resulting_resolution,[],[f4639,f4646,f4824])).

fof(f4824,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3533])).

fof(f3533,plain,(
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

fof(f4646,plain,(
    m1_pre_topc(sK99,sK96) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4137,plain,
    ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,sK101) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,sK100),sK101)
    & r2_hidden(sK101,u1_struct_0(sK98))
    & m1_subset_1(sK101,u1_struct_0(sK99))
    & m1_pre_topc(sK98,sK99)
    & m1_subset_1(sK100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK99),u1_struct_0(sK97))))
    & v1_funct_2(sK100,u1_struct_0(sK99),u1_struct_0(sK97))
    & v1_funct_1(sK100)
    & m1_pre_topc(sK99,sK96)
    & ~ v2_struct_0(sK99)
    & m1_pre_topc(sK98,sK96)
    & ~ v2_struct_0(sK98)
    & l1_pre_topc(sK97)
    & v2_pre_topc(sK97)
    & ~ v2_struct_0(sK97)
    & l1_pre_topc(sK96)
    & v2_pre_topc(sK96)
    & ~ v2_struct_0(sK96) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK96,sK97,sK98,sK99,sK100,sK101])],[f3439,f4136,f4135,f4134,f4133,f4132,f4131])).

fof(f4131,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                            & r2_hidden(X5,u1_struct_0(X2))
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & m1_pre_topc(X2,X3)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK96,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK96)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK96)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK96)
      & v2_pre_topc(sK96)
      & ~ v2_struct_0(sK96) ) ),
    introduced(choice_axiom,[])).

fof(f4132,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(sK96,X1,X3,X2,X4),X5)
                        & r2_hidden(X5,u1_struct_0(X2))
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & m1_pre_topc(X2,X3)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK96)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK96)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,X3,X2,X4),X5)
                      & r2_hidden(X5,u1_struct_0(X2))
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & m1_pre_topc(X2,X3)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK97))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK97))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK96)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK96)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK97)
      & v2_pre_topc(sK97)
      & ~ v2_struct_0(sK97) ) ),
    introduced(choice_axiom,[])).

fof(f4133,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,X3,X2,X4),X5)
                    & r2_hidden(X5,u1_struct_0(X2))
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & m1_pre_topc(X2,X3)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK97))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK97))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK96)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK96)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,X3,sK98,X4),X5)
                  & r2_hidden(X5,u1_struct_0(sK98))
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & m1_pre_topc(sK98,X3)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK97))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK97))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK96)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK98,sK96)
      & ~ v2_struct_0(sK98) ) ),
    introduced(choice_axiom,[])).

fof(f4134,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(u1_struct_0(X3),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,X3,sK98,X4),X5)
                & r2_hidden(X5,u1_struct_0(sK98))
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & m1_pre_topc(sK98,X3)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK97))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK97))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK96)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,X4),X5)
              & r2_hidden(X5,u1_struct_0(sK98))
              & m1_subset_1(X5,u1_struct_0(sK99)) )
          & m1_pre_topc(sK98,sK99)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK99),u1_struct_0(sK97))))
          & v1_funct_2(X4,u1_struct_0(sK99),u1_struct_0(sK97))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK99,sK96)
      & ~ v2_struct_0(sK99) ) ),
    introduced(choice_axiom,[])).

fof(f4135,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),X4,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,X4),X5)
            & r2_hidden(X5,u1_struct_0(sK98))
            & m1_subset_1(X5,u1_struct_0(sK99)) )
        & m1_pre_topc(sK98,sK99)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK99),u1_struct_0(sK97))))
        & v1_funct_2(X4,u1_struct_0(sK99),u1_struct_0(sK97))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,sK100),X5)
          & r2_hidden(X5,u1_struct_0(sK98))
          & m1_subset_1(X5,u1_struct_0(sK99)) )
      & m1_pre_topc(sK98,sK99)
      & m1_subset_1(sK100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK99),u1_struct_0(sK97))))
      & v1_funct_2(sK100,u1_struct_0(sK99),u1_struct_0(sK97))
      & v1_funct_1(sK100) ) ),
    introduced(choice_axiom,[])).

fof(f4136,plain,
    ( ? [X5] :
        ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,X5) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,sK100),X5)
        & r2_hidden(X5,u1_struct_0(sK98))
        & m1_subset_1(X5,u1_struct_0(sK99)) )
   => ( k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,sK101) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,sK100),sK101)
      & r2_hidden(sK101,u1_struct_0(sK98))
      & m1_subset_1(sK101,u1_struct_0(sK99)) ) ),
    introduced(choice_axiom,[])).

fof(f3439,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3438])).

fof(f3438,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) != k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5)
                          & r2_hidden(X5,u1_struct_0(X2))
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & m1_pre_topc(X2,X3)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3424])).

fof(f3424,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X2,X3)
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ( r2_hidden(X5,u1_struct_0(X2))
                               => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3423])).

fof(f3423,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X2,X3)
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ( r2_hidden(X5,u1_struct_0(X2))
                             => k3_funct_2(u1_struct_0(X3),u1_struct_0(X1),X4,X5) = k1_funct_1(k3_tmap_1(X0,X1,X3,X2,X4),X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tmap_1)).

fof(f4639,plain,(
    l1_pre_topc(sK96) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4650,plain,(
    m1_pre_topc(sK98,sK99) ),
    inference(cnf_transformation,[],[f4137])).

fof(f16511,plain,(
    ~ m1_subset_1(u1_struct_0(sK98),k1_zfmisc_1(u1_struct_0(sK99))) ),
    inference(unit_resulting_resolution,[],[f7549,f13090,f5821])).

fof(f5821,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP274(X1) ) ),
    inference(cnf_transformation,[],[f5821_D])).

fof(f5821_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP274(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP274])])).

fof(f13090,plain,(
    v1_xboole_0(u1_struct_0(sK99)) ),
    inference(unit_resulting_resolution,[],[f4647,f4651,f4648,f4649,f12871,f4764])).

fof(f4764,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3481])).

fof(f3481,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3480])).

fof(f3480,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1555])).

fof(f1555,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k1_funct_1(X2,X3) = k3_funct_2(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f12871,plain,(
    k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,sK101) != k1_funct_1(sK100,sK101) ),
    inference(backward_demodulation,[],[f11686,f12000])).

fof(f12000,plain,(
    k1_funct_1(sK100,sK101) = k1_funct_1(k7_relat_1(sK100,u1_struct_0(sK98)),sK101) ),
    inference(unit_resulting_resolution,[],[f4652,f4647,f11417,f5396])).

fof(f5396,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f3832])).

fof(f3832,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f3831])).

fof(f3831,plain,(
    ! [X0,X1,X2] :
      ( k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0)
      | ~ r2_hidden(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1042])).

fof(f1042,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,X1)
       => k1_funct_1(X2,X0) = k1_funct_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_funct_1)).

fof(f11417,plain,(
    v1_relat_1(sK100) ),
    inference(unit_resulting_resolution,[],[f4800,f4649,f5024])).

fof(f5024,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f3609])).

fof(f3609,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f4800,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f4652,plain,(
    r2_hidden(sK101,u1_struct_0(sK98)) ),
    inference(cnf_transformation,[],[f4137])).

fof(f11686,plain,(
    k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,sK101) != k1_funct_1(k7_relat_1(sK100,u1_struct_0(sK98)),sK101) ),
    inference(backward_demodulation,[],[f4653,f11685])).

fof(f11685,plain,(
    k3_tmap_1(sK96,sK97,sK99,sK98,sK100) = k7_relat_1(sK100,u1_struct_0(sK98)) ),
    inference(forward_demodulation,[],[f11377,f11391])).

fof(f11391,plain,(
    ! [X0] : k7_relat_1(sK100,X0) = k2_partfun1(u1_struct_0(sK99),u1_struct_0(sK97),sK100,X0) ),
    inference(unit_resulting_resolution,[],[f4647,f4649,f5123])).

fof(f5123,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3674])).

fof(f3674,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3673])).

fof(f3673,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1554])).

fof(f1554,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f11377,plain,(
    k3_tmap_1(sK96,sK97,sK99,sK98,sK100) = k2_partfun1(u1_struct_0(sK99),u1_struct_0(sK97),sK100,u1_struct_0(sK98)) ),
    inference(unit_resulting_resolution,[],[f4637,f4638,f4639,f4640,f4641,f4642,f4646,f4644,f4647,f4650,f4648,f4649,f4763])).

fof(f4763,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3479])).

fof(f3479,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3478])).

fof(f3478,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3331])).

fof(f3331,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f4644,plain,(
    m1_pre_topc(sK98,sK96) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4642,plain,(
    l1_pre_topc(sK97) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4641,plain,(
    v2_pre_topc(sK97) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4640,plain,(
    ~ v2_struct_0(sK97) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4638,plain,(
    v2_pre_topc(sK96) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4637,plain,(
    ~ v2_struct_0(sK96) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4653,plain,(
    k3_funct_2(u1_struct_0(sK99),u1_struct_0(sK97),sK100,sK101) != k1_funct_1(k3_tmap_1(sK96,sK97,sK99,sK98,sK100),sK101) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4649,plain,(
    m1_subset_1(sK100,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK99),u1_struct_0(sK97)))) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4648,plain,(
    v1_funct_2(sK100,u1_struct_0(sK99),u1_struct_0(sK97)) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4651,plain,(
    m1_subset_1(sK101,u1_struct_0(sK99)) ),
    inference(cnf_transformation,[],[f4137])).

fof(f4647,plain,(
    v1_funct_1(sK100) ),
    inference(cnf_transformation,[],[f4137])).

fof(f7549,plain,(
    ~ sP274(u1_struct_0(sK98)) ),
    inference(unit_resulting_resolution,[],[f4652,f5822])).

fof(f5822,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP274(X1) ) ),
    inference(general_splitting,[],[f5098,f5821_D])).

fof(f5098,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f3655])).

fof(f3655,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
%------------------------------------------------------------------------------
