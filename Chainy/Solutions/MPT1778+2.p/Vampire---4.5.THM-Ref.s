%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1778+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 37.89s
% Output     : Refutation 37.89s
% Verified   : 
% Statistics : Number of formulae       :   87 (1878 expanded)
%              Number of leaves         :   15 ( 959 expanded)
%              Depth                    :   17
%              Number of atoms          :  564 (36603 expanded)
%              Number of equality atoms :   19 (  82 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f46986,plain,(
    $false ),
    inference(subsumption_resolution,[],[f46985,f15004])).

fof(f15004,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK31,X0)) ),
    inference(backward_demodulation,[],[f11309,f14981])).

fof(f14981,plain,(
    ! [X0] : k7_relat_1(sK31,X0) = k2_partfun1(u1_struct_0(sK29),u1_struct_0(sK28),sK31,X0) ),
    inference(unit_resulting_resolution,[],[f4514,f4517,f5035])).

fof(f5035,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3803])).

fof(f3803,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3802])).

fof(f3802,plain,(
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

fof(f4517,plain,(
    m1_subset_1(sK31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28)))) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4099,plain,
    ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
      | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),sK30,sK28)
      | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
      | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) )
    & m1_pre_topc(sK30,sK29)
    & m1_subset_1(sK31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
    & v5_pre_topc(sK31,sK29,sK28)
    & v1_funct_2(sK31,u1_struct_0(sK29),u1_struct_0(sK28))
    & v1_funct_1(sK31)
    & m1_pre_topc(sK30,sK27)
    & ~ v2_struct_0(sK30)
    & m1_pre_topc(sK29,sK27)
    & ~ v2_struct_0(sK29)
    & l1_pre_topc(sK28)
    & v2_pre_topc(sK28)
    & ~ v2_struct_0(sK28)
    & l1_pre_topc(sK27)
    & v2_pre_topc(sK27)
    & ~ v2_struct_0(sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27,sK28,sK29,sK30,sK31])],[f3455,f4098,f4097,f4096,f4095,f4094])).

fof(f4094,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                        & m1_pre_topc(X3,X2)
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
                      ( ( ~ m1_subset_1(k3_tmap_1(sK27,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(sK27,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(sK27,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(sK27,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK27)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK27)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK27)
      & v2_pre_topc(sK27)
      & ~ v2_struct_0(sK27) ) ),
    introduced(choice_axiom,[])).

fof(f4095,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ m1_subset_1(k3_tmap_1(sK27,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      | ~ v5_pre_topc(k3_tmap_1(sK27,X1,X2,X3,X4),X3,X1)
                      | ~ v1_funct_2(k3_tmap_1(sK27,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                      | ~ v1_funct_1(k3_tmap_1(sK27,X1,X2,X3,X4)) )
                    & m1_pre_topc(X3,X2)
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v5_pre_topc(X4,X2,X1)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK27)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK27)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK28))))
                    | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,X2,X3,X4),X3,sK28)
                    | ~ v1_funct_2(k3_tmap_1(sK27,sK28,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK28))
                    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,X2,X3,X4)) )
                  & m1_pre_topc(X3,X2)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK28))))
                  & v5_pre_topc(X4,X2,sK28)
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK28))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK27)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK27)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK28)
      & v2_pre_topc(sK28)
      & ~ v2_struct_0(sK28) ) ),
    introduced(choice_axiom,[])).

fof(f4096,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK28))))
                  | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,X2,X3,X4),X3,sK28)
                  | ~ v1_funct_2(k3_tmap_1(sK27,sK28,X2,X3,X4),u1_struct_0(X3),u1_struct_0(sK28))
                  | ~ v1_funct_1(k3_tmap_1(sK27,sK28,X2,X3,X4)) )
                & m1_pre_topc(X3,X2)
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK28))))
                & v5_pre_topc(X4,X2,sK28)
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK28))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK27)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK27)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK28))))
                | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,X3,X4),X3,sK28)
                | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,X3,X4),u1_struct_0(X3),u1_struct_0(sK28))
                | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,X3,X4)) )
              & m1_pre_topc(X3,sK29)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
              & v5_pre_topc(X4,sK29,sK28)
              & v1_funct_2(X4,u1_struct_0(sK29),u1_struct_0(sK28))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK27)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK29,sK27)
      & ~ v2_struct_0(sK29) ) ),
    introduced(choice_axiom,[])).

fof(f4097,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK28))))
              | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,X3,X4),X3,sK28)
              | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,X3,X4),u1_struct_0(X3),u1_struct_0(sK28))
              | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,X3,X4)) )
            & m1_pre_topc(X3,sK29)
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
            & v5_pre_topc(X4,sK29,sK28)
            & v1_funct_2(X4,u1_struct_0(sK29),u1_struct_0(sK28))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK27)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,sK30,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
            | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,X4),sK30,sK28)
            | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,X4),u1_struct_0(sK30),u1_struct_0(sK28))
            | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,X4)) )
          & m1_pre_topc(sK30,sK29)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
          & v5_pre_topc(X4,sK29,sK28)
          & v1_funct_2(X4,u1_struct_0(sK29),u1_struct_0(sK28))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK30,sK27)
      & ~ v2_struct_0(sK30) ) ),
    introduced(choice_axiom,[])).

fof(f4098,plain,
    ( ? [X4] :
        ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,sK30,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
          | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,X4),sK30,sK28)
          | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,X4),u1_struct_0(sK30),u1_struct_0(sK28))
          | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,X4)) )
        & m1_pre_topc(sK30,sK29)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
        & v5_pre_topc(X4,sK29,sK28)
        & v1_funct_2(X4,u1_struct_0(sK29),u1_struct_0(sK28))
        & v1_funct_1(X4) )
   => ( ( ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
        | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),sK30,sK28)
        | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
        | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) )
      & m1_pre_topc(sK30,sK29)
      & m1_subset_1(sK31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK29),u1_struct_0(sK28))))
      & v5_pre_topc(sK31,sK29,sK28)
      & v1_funct_2(sK31,u1_struct_0(sK29),u1_struct_0(sK28))
      & v1_funct_1(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f3455,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(flattening,[],[f3454])).

fof(f3454,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        | ~ v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                        | ~ v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                        | ~ v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
                      & m1_pre_topc(X3,X2)
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v5_pre_topc(X4,X2,X1)
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
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
    inference(ennf_transformation,[],[f3444])).

fof(f3444,negated_conjecture,(
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
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                          & v5_pre_topc(X4,X2,X1)
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( m1_pre_topc(X3,X2)
                         => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                            & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                            & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                            & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3443])).

fof(f3443,conjecture,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v5_pre_topc(X4,X2,X1)
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v5_pre_topc(k3_tmap_1(X0,X1,X2,X3,X4),X3,X1)
                          & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_tmap_1)).

fof(f4514,plain,(
    v1_funct_1(sK31) ),
    inference(cnf_transformation,[],[f4099])).

fof(f11309,plain,(
    ! [X0] : v1_funct_1(k2_partfun1(u1_struct_0(sK29),u1_struct_0(sK28),sK31,X0)) ),
    inference(unit_resulting_resolution,[],[f4514,f4517,f5033])).

fof(f5033,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f3801])).

fof(f3801,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3800])).

fof(f3800,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1500])).

fof(f1500,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f46985,plain,(
    ~ v1_funct_1(k7_relat_1(sK31,u1_struct_0(sK30))) ),
    inference(forward_demodulation,[],[f46984,f46969])).

fof(f46969,plain,(
    k3_tmap_1(sK27,sK28,sK29,sK30,sK31) = k7_relat_1(sK31,u1_struct_0(sK30)) ),
    inference(forward_demodulation,[],[f46672,f14981])).

fof(f46672,plain,(
    k3_tmap_1(sK27,sK28,sK29,sK30,sK31) = k2_partfun1(u1_struct_0(sK29),u1_struct_0(sK28),sK31,u1_struct_0(sK30)) ),
    inference(unit_resulting_resolution,[],[f4504,f4505,f4506,f4507,f4508,f4509,f4511,f4513,f4514,f4518,f4515,f4517,f4541])).

fof(f4541,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3485])).

fof(f3485,plain,(
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
    inference(flattening,[],[f3484])).

fof(f3484,plain,(
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

fof(f4515,plain,(
    v1_funct_2(sK31,u1_struct_0(sK29),u1_struct_0(sK28)) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4518,plain,(
    m1_pre_topc(sK30,sK29) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4513,plain,(
    m1_pre_topc(sK30,sK27) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4511,plain,(
    m1_pre_topc(sK29,sK27) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4509,plain,(
    l1_pre_topc(sK28) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4508,plain,(
    v2_pre_topc(sK28) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4507,plain,(
    ~ v2_struct_0(sK28) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4506,plain,(
    l1_pre_topc(sK27) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4505,plain,(
    v2_pre_topc(sK27) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4504,plain,(
    ~ v2_struct_0(sK27) ),
    inference(cnf_transformation,[],[f4099])).

fof(f46984,plain,(
    ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(subsumption_resolution,[],[f46983,f46487])).

fof(f46487,plain,(
    v1_funct_2(k7_relat_1(sK31,u1_struct_0(sK30)),u1_struct_0(sK30),u1_struct_0(sK28)) ),
    inference(forward_demodulation,[],[f46481,f46386])).

fof(f46386,plain,(
    k2_tmap_1(sK29,sK28,sK31,sK30) = k7_relat_1(sK31,u1_struct_0(sK30)) ),
    inference(forward_demodulation,[],[f46306,f14981])).

fof(f46306,plain,(
    k2_tmap_1(sK29,sK28,sK31,sK30) = k2_partfun1(u1_struct_0(sK29),u1_struct_0(sK28),sK31,u1_struct_0(sK30)) ),
    inference(unit_resulting_resolution,[],[f4510,f6720,f5779,f4507,f4508,f4509,f4514,f4518,f4515,f4517,f4653])).

fof(f4653,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3574])).

fof(f3574,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3573])).

fof(f3573,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3330])).

fof(f3330,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f5779,plain,(
    l1_pre_topc(sK29) ),
    inference(unit_resulting_resolution,[],[f4511,f4506,f4620])).

fof(f4620,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3544])).

fof(f3544,plain,(
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

fof(f6720,plain,(
    v2_pre_topc(sK29) ),
    inference(unit_resulting_resolution,[],[f4506,f4511,f4505,f4611])).

fof(f4611,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3534])).

fof(f3534,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3533])).

fof(f3533,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1760])).

fof(f1760,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f4510,plain,(
    ~ v2_struct_0(sK29) ),
    inference(cnf_transformation,[],[f4099])).

fof(f46481,plain,(
    v1_funct_2(k2_tmap_1(sK29,sK28,sK31,sK30),u1_struct_0(sK30),u1_struct_0(sK28)) ),
    inference(unit_resulting_resolution,[],[f4510,f6720,f5779,f4507,f4508,f4509,f4514,f4512,f4518,f4516,f4515,f4517,f4646])).

fof(f4646,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3566])).

fof(f3566,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3565])).

fof(f3565,plain,(
    ! [X0,X1,X2,X3] :
      ( ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3341])).

fof(f3341,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v5_pre_topc(X2,X0,X1)
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tmap_1)).

fof(f4516,plain,(
    v5_pre_topc(sK31,sK29,sK28) ),
    inference(cnf_transformation,[],[f4099])).

fof(f4512,plain,(
    ~ v2_struct_0(sK30) ),
    inference(cnf_transformation,[],[f4099])).

fof(f46983,plain,
    ( ~ v1_funct_2(k7_relat_1(sK31,u1_struct_0(sK30)),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(forward_demodulation,[],[f46982,f46969])).

fof(f46982,plain,
    ( ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(subsumption_resolution,[],[f46981,f46387])).

fof(f46387,plain,(
    v5_pre_topc(k7_relat_1(sK31,u1_struct_0(sK30)),sK30,sK28) ),
    inference(backward_demodulation,[],[f46298,f46386])).

fof(f46298,plain,(
    v5_pre_topc(k2_tmap_1(sK29,sK28,sK31,sK30),sK30,sK28) ),
    inference(unit_resulting_resolution,[],[f4510,f6720,f5779,f4507,f4508,f4509,f4514,f4512,f4518,f4516,f4515,f4517,f4647])).

fof(f4647,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(k2_tmap_1(X0,X1,X2,X3),X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3566])).

fof(f46981,plain,
    ( ~ v5_pre_topc(k7_relat_1(sK31,u1_struct_0(sK30)),sK30,sK28)
    | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(forward_demodulation,[],[f46980,f46969])).

fof(f46980,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),sK30,sK28)
    | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(subsumption_resolution,[],[f46970,f46966])).

fof(f46966,plain,(
    m1_subset_1(k7_relat_1(sK31,u1_struct_0(sK30)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28)))) ),
    inference(backward_demodulation,[],[f46407,f46965])).

fof(f46965,plain,(
    k3_tmap_1(sK29,sK28,sK29,sK30,sK31) = k7_relat_1(sK31,u1_struct_0(sK30)) ),
    inference(forward_demodulation,[],[f46673,f14981])).

fof(f46673,plain,(
    k3_tmap_1(sK29,sK28,sK29,sK30,sK31) = k2_partfun1(u1_struct_0(sK29),u1_struct_0(sK28),sK31,u1_struct_0(sK30)) ),
    inference(unit_resulting_resolution,[],[f4510,f6720,f5779,f4507,f4508,f4509,f5799,f4518,f4514,f4518,f4515,f4517,f4541])).

fof(f5799,plain,(
    m1_pre_topc(sK29,sK29) ),
    inference(unit_resulting_resolution,[],[f5779,f4621])).

fof(f4621,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3545])).

fof(f3545,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3377])).

fof(f3377,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f46407,plain,(
    m1_subset_1(k3_tmap_1(sK29,sK28,sK29,sK30,sK31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28)))) ),
    inference(unit_resulting_resolution,[],[f4510,f6720,f5779,f4507,f4508,f4509,f4518,f5799,f4514,f4515,f4517,f4522])).

fof(f4522,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3457])).

fof(f3457,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(flattening,[],[f3456])).

fof(f3456,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) )
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
    inference(ennf_transformation,[],[f3337])).

fof(f3337,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & m1_pre_topc(X2,X0)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k3_tmap_1(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k3_tmap_1(X0,X1,X2,X3,X4),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k3_tmap_1(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_tmap_1)).

fof(f46970,plain,
    ( ~ m1_subset_1(k7_relat_1(sK31,u1_struct_0(sK30)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
    | ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),sK30,sK28)
    | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(backward_demodulation,[],[f4519,f46969])).

fof(f4519,plain,
    ( ~ v5_pre_topc(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),sK30,sK28)
    | ~ m1_subset_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK30),u1_struct_0(sK28))))
    | ~ v1_funct_2(k3_tmap_1(sK27,sK28,sK29,sK30,sK31),u1_struct_0(sK30),u1_struct_0(sK28))
    | ~ v1_funct_1(k3_tmap_1(sK27,sK28,sK29,sK30,sK31)) ),
    inference(cnf_transformation,[],[f4099])).
%------------------------------------------------------------------------------
