%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1770+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:32 EST 2020

% Result     : Theorem 6.70s
% Output     : Refutation 6.70s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 688 expanded)
%              Number of leaves         :   14 ( 401 expanded)
%              Depth                    :   10
%              Number of atoms          :  497 (12711 expanded)
%              Number of equality atoms :   41 ( 959 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7774,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7773,f7731])).

fof(f7731,plain,(
    ~ r1_tmap_1(sK19,sK17,k7_relat_1(sK20,u1_struct_0(sK19)),sK21) ),
    inference(backward_demodulation,[],[f4826,f7727])).

fof(f7727,plain,(
    k3_tmap_1(sK16,sK17,sK18,sK19,sK20) = k7_relat_1(sK20,u1_struct_0(sK19)) ),
    inference(forward_demodulation,[],[f7707,f6279])).

fof(f6279,plain,(
    ! [X0] : k2_partfun1(u1_struct_0(sK18),u1_struct_0(sK17),sK20,X0) = k7_relat_1(sK20,X0) ),
    inference(unit_resulting_resolution,[],[f4139,f4141,f4483])).

fof(f4483,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f3689])).

fof(f3689,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k2_partfun1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3688])).

fof(f3688,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f4141,plain,(
    m1_subset_1(sK20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17)))) ),
    inference(cnf_transformation,[],[f3857])).

fof(f3857,plain,
    ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),sK22)
    & r1_tmap_1(sK18,sK17,sK20,sK21)
    & m1_pre_topc(sK19,sK18)
    & sK21 = sK22
    & m1_subset_1(sK22,u1_struct_0(sK19))
    & m1_subset_1(sK21,u1_struct_0(sK18))
    & m1_subset_1(sK20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
    & v1_funct_2(sK20,u1_struct_0(sK18),u1_struct_0(sK17))
    & v1_funct_1(sK20)
    & m1_pre_topc(sK19,sK16)
    & ~ v2_struct_0(sK19)
    & m1_pre_topc(sK18,sK16)
    & ~ v2_struct_0(sK18)
    & l1_pre_topc(sK17)
    & v2_pre_topc(sK17)
    & ~ v2_struct_0(sK17)
    & l1_pre_topc(sK16)
    & v2_pre_topc(sK16)
    & ~ v2_struct_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16,sK17,sK18,sK19,sK20,sK21,sK22])],[f3443,f3856,f3855,f3854,f3853,f3852,f3851,f3850])).

fof(f3850,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                                & r1_tmap_1(X2,X1,X4,X5)
                                & m1_pre_topc(X3,X2)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X3)) )
                            & m1_subset_1(X5,u1_struct_0(X2)) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,k3_tmap_1(sK16,X1,X2,X3,X4),X6)
                              & r1_tmap_1(X2,X1,X4,X5)
                              & m1_pre_topc(X3,X2)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK16)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK16)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK16)
      & v2_pre_topc(sK16)
      & ~ v2_struct_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f3851,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,k3_tmap_1(sK16,X1,X2,X3,X4),X6)
                            & r1_tmap_1(X2,X1,X4,X5)
                            & m1_pre_topc(X3,X2)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X3)) )
                        & m1_subset_1(X5,u1_struct_0(X2)) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK16)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK16)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK17,k3_tmap_1(sK16,sK17,X2,X3,X4),X6)
                          & r1_tmap_1(X2,sK17,X4,X5)
                          & m1_pre_topc(X3,X2)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X3)) )
                      & m1_subset_1(X5,u1_struct_0(X2)) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK17))))
                  & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK17))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK16)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK16)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK17)
      & v2_pre_topc(sK17)
      & ~ v2_struct_0(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f3852,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK17,k3_tmap_1(sK16,sK17,X2,X3,X4),X6)
                        & r1_tmap_1(X2,sK17,X4,X5)
                        & m1_pre_topc(X3,X2)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X3)) )
                    & m1_subset_1(X5,u1_struct_0(X2)) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(sK17))))
                & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(sK17))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK16)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK16)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK17,k3_tmap_1(sK16,sK17,sK18,X3,X4),X6)
                      & r1_tmap_1(sK18,sK17,X4,X5)
                      & m1_pre_topc(X3,sK18)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(X3)) )
                  & m1_subset_1(X5,u1_struct_0(sK18)) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
              & v1_funct_2(X4,u1_struct_0(sK18),u1_struct_0(sK17))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK16)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK18,sK16)
      & ~ v2_struct_0(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f3853,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK17,k3_tmap_1(sK16,sK17,sK18,X3,X4),X6)
                    & r1_tmap_1(sK18,sK17,X4,X5)
                    & m1_pre_topc(X3,sK18)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(X3)) )
                & m1_subset_1(X5,u1_struct_0(sK18)) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
            & v1_funct_2(X4,u1_struct_0(sK18),u1_struct_0(sK17))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK16)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,X4),X6)
                  & r1_tmap_1(sK18,sK17,X4,X5)
                  & m1_pre_topc(sK19,sK18)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK19)) )
              & m1_subset_1(X5,u1_struct_0(sK18)) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
          & v1_funct_2(X4,u1_struct_0(sK18),u1_struct_0(sK17))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK19,sK16)
      & ~ v2_struct_0(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f3854,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,X4),X6)
                & r1_tmap_1(sK18,sK17,X4,X5)
                & m1_pre_topc(sK19,sK18)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK19)) )
            & m1_subset_1(X5,u1_struct_0(sK18)) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
        & v1_funct_2(X4,u1_struct_0(sK18),u1_struct_0(sK17))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),X6)
              & r1_tmap_1(sK18,sK17,sK20,X5)
              & m1_pre_topc(sK19,sK18)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK19)) )
          & m1_subset_1(X5,u1_struct_0(sK18)) )
      & m1_subset_1(sK20,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK18),u1_struct_0(sK17))))
      & v1_funct_2(sK20,u1_struct_0(sK18),u1_struct_0(sK17))
      & v1_funct_1(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f3855,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),X6)
            & r1_tmap_1(sK18,sK17,sK20,X5)
            & m1_pre_topc(sK19,sK18)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK19)) )
        & m1_subset_1(X5,u1_struct_0(sK18)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),X6)
          & r1_tmap_1(sK18,sK17,sK20,sK21)
          & m1_pre_topc(sK19,sK18)
          & sK21 = X6
          & m1_subset_1(X6,u1_struct_0(sK19)) )
      & m1_subset_1(sK21,u1_struct_0(sK18)) ) ),
    introduced(choice_axiom,[])).

fof(f3856,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),X6)
        & r1_tmap_1(sK18,sK17,sK20,sK21)
        & m1_pre_topc(sK19,sK18)
        & sK21 = X6
        & m1_subset_1(X6,u1_struct_0(sK19)) )
   => ( ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),sK22)
      & r1_tmap_1(sK18,sK17,sK20,sK21)
      & m1_pre_topc(sK19,sK18)
      & sK21 = sK22
      & m1_subset_1(sK22,u1_struct_0(sK19)) ) ),
    introduced(choice_axiom,[])).

fof(f3443,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              & r1_tmap_1(X2,X1,X4,X5)
                              & m1_pre_topc(X3,X2)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(flattening,[],[f3442])).

fof(f3442,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6)
                              & r1_tmap_1(X2,X1,X4,X5)
                              & m1_pre_topc(X3,X2)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X3)) )
                          & m1_subset_1(X5,u1_struct_0(X2)) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
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
    inference(ennf_transformation,[],[f3435])).

fof(f3435,negated_conjecture,(
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
                          & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X2))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X3))
                               => ( ( r1_tmap_1(X2,X1,X4,X5)
                                    & m1_pre_topc(X3,X2)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3434])).

fof(f3434,conjecture,(
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
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X2))
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X3))
                             => ( ( r1_tmap_1(X2,X1,X4,X5)
                                  & m1_pre_topc(X3,X2)
                                  & X5 = X6 )
                               => r1_tmap_1(X3,X1,k3_tmap_1(X0,X1,X2,X3,X4),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tmap_1)).

fof(f4139,plain,(
    v1_funct_1(sK20) ),
    inference(cnf_transformation,[],[f3857])).

fof(f7707,plain,(
    k3_tmap_1(sK16,sK17,sK18,sK19,sK20) = k2_partfun1(u1_struct_0(sK18),u1_struct_0(sK17),sK20,u1_struct_0(sK19)) ),
    inference(unit_resulting_resolution,[],[f4129,f4130,f4131,f4132,f4133,f4134,f4136,f4138,f4139,f4145,f4140,f4141,f4163])).

fof(f4163,plain,(
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
    inference(cnf_transformation,[],[f3465])).

fof(f3465,plain,(
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
    inference(flattening,[],[f3464])).

fof(f3464,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f4140,plain,(
    v1_funct_2(sK20,u1_struct_0(sK18),u1_struct_0(sK17)) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4145,plain,(
    m1_pre_topc(sK19,sK18) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4138,plain,(
    m1_pre_topc(sK19,sK16) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4136,plain,(
    m1_pre_topc(sK18,sK16) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4134,plain,(
    l1_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4133,plain,(
    v2_pre_topc(sK17) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4132,plain,(
    ~ v2_struct_0(sK17) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4131,plain,(
    l1_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4130,plain,(
    v2_pre_topc(sK16) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4129,plain,(
    ~ v2_struct_0(sK16) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4826,plain,(
    ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),sK21) ),
    inference(backward_demodulation,[],[f4147,f4144])).

fof(f4144,plain,(
    sK21 = sK22 ),
    inference(cnf_transformation,[],[f3857])).

fof(f4147,plain,(
    ~ r1_tmap_1(sK19,sK17,k3_tmap_1(sK16,sK17,sK18,sK19,sK20),sK22) ),
    inference(cnf_transformation,[],[f3857])).

fof(f7773,plain,(
    r1_tmap_1(sK19,sK17,k7_relat_1(sK20,u1_struct_0(sK19)),sK21) ),
    inference(forward_demodulation,[],[f7771,f7562])).

fof(f7562,plain,(
    k2_tmap_1(sK18,sK17,sK20,sK19) = k7_relat_1(sK20,u1_struct_0(sK19)) ),
    inference(forward_demodulation,[],[f7557,f6279])).

fof(f7557,plain,(
    k2_tmap_1(sK18,sK17,sK20,sK19) = k2_partfun1(u1_struct_0(sK18),u1_struct_0(sK17),sK20,u1_struct_0(sK19)) ),
    inference(unit_resulting_resolution,[],[f4135,f5144,f4939,f4132,f4133,f4134,f4139,f4145,f4140,f4141,f4263])).

fof(f4263,plain,(
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
    inference(cnf_transformation,[],[f3542])).

fof(f3542,plain,(
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
    inference(flattening,[],[f3541])).

fof(f3541,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(f4939,plain,(
    l1_pre_topc(sK18) ),
    inference(unit_resulting_resolution,[],[f4136,f4131,f4235])).

fof(f4235,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3518])).

fof(f3518,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f5144,plain,(
    v2_pre_topc(sK18) ),
    inference(unit_resulting_resolution,[],[f4131,f4136,f4130,f4226])).

fof(f4226,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3508])).

fof(f3508,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3507])).

fof(f3507,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f4135,plain,(
    ~ v2_struct_0(sK18) ),
    inference(cnf_transformation,[],[f3857])).

fof(f7771,plain,(
    r1_tmap_1(sK19,sK17,k2_tmap_1(sK18,sK17,sK20,sK19),sK21) ),
    inference(unit_resulting_resolution,[],[f4132,f4133,f4134,f4135,f5144,f4939,f4139,f4137,f4145,f4827,f4142,f4146,f4140,f4141,f4691])).

fof(f4691,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f4168])).

fof(f4168,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | X4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3471])).

fof(f3471,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3470])).

% (11885)Termination reason: Time limit

% (11885)Memory used [KB]: 17910
% (11885)Time elapsed: 0.810 s
% (11885)------------------------------
% (11885)------------------------------
fof(f3470,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3415])).

fof(f3415,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

fof(f4146,plain,(
    r1_tmap_1(sK18,sK17,sK20,sK21) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4142,plain,(
    m1_subset_1(sK21,u1_struct_0(sK18)) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4827,plain,(
    m1_subset_1(sK21,u1_struct_0(sK19)) ),
    inference(forward_demodulation,[],[f4143,f4144])).

fof(f4143,plain,(
    m1_subset_1(sK22,u1_struct_0(sK19)) ),
    inference(cnf_transformation,[],[f3857])).

fof(f4137,plain,(
    ~ v2_struct_0(sK19) ),
    inference(cnf_transformation,[],[f3857])).
%------------------------------------------------------------------------------
