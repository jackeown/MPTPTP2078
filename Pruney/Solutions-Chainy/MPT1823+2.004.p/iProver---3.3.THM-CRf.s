%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:23 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  239 (3120 expanded)
%              Number of clauses        :  166 ( 720 expanded)
%              Number of leaves         :   18 (1259 expanded)
%              Depth                    :   34
%              Number of atoms          : 1621 (37902 expanded)
%              Number of equality atoms :  638 (3970 expanded)
%              Maximal formula depth    :   24 (   8 average)
%              Maximal clause size      :   30 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( l1_struct_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(X2)
        & l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) )
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,conjecture,(
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
                 => ( k1_tsep_1(X0,X2,X3) = X0
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
                   => ( k1_tsep_1(X0,X2,X3) = X0
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                            & v1_funct_1(X4) )
                         => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
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
    inference(flattening,[],[f33])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X4) )
     => ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3)))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X4) )
          & k1_tsep_1(X0,X2,X3) = X0
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3)))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
            & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
            & v1_funct_1(X4) )
        & k1_tsep_1(X0,X2,sK3) = X0
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X4) )
              & k1_tsep_1(X0,X2,X3) = X0
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3)))
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X4) )
            & k1_tsep_1(X0,sK2,X3) = X0
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(X0,X2,X3) = X0
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3)))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
                    & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1))
                    & v1_funct_1(X4) )
                & k1_tsep_1(X0,X2,X3) = X0
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(sK1)
        & v2_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & k1_tsep_1(X0,X2,X3) = X0
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
                      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3)))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & k1_tsep_1(sK0,X2,X3) = sK0
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK4)
    & k1_tsep_1(sK0,sK2,sK3) = sK0
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).

fof(f69,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
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
                       => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)
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
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f64,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f65,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f71,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f59,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f70,plain,(
    k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
        & v1_funct_1(X4)
        & m1_pre_topc(X3,X0)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
        & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
        & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_funct_2(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(k2_tmap_1(X0,X1,X2,X3))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1))
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
      | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_2(X5,X2,X3)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X4,X0,X1)
        & v1_funct_1(X4)
        & ~ v1_xboole_0(X3)
        & ~ v1_xboole_0(X1) )
     => ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      <=> X4 = X5 )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( ( r1_funct_2(X0,X1,X2,X3,X4,X5)
          | X4 != X5 )
        & ( X4 = X5
          | ~ r1_funct_2(X0,X1,X2,X3,X4,X5) ) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X4,X5)
      | X4 != X5
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X4,X0,X1)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_funct_2(X0,X1,X2,X3,X5,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_2(X5,X2,X3)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X5,X0,X1)
      | ~ v1_funct_1(X5)
      | v1_xboole_0(X3)
      | v1_xboole_0(X1) ) ),
    inference(equality_resolution,[],[f49])).

fof(f74,plain,(
    ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_736,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X2_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1340,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
    | l1_struct_0(X1_54) != iProver_top
    | l1_struct_0(X2_54) != iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_727,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1348,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_731,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1345,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X4)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X1,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1336,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_3021,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1336])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_35,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_36,plain,
    ( v2_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_37,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_43,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3515,plain,
    ( v2_struct_0(X1_54) = iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3021,c_35,c_36,c_37,c_42,c_43])).

cnf(c_3516,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
    | m1_pre_topc(X0_54,X1_54) != iProver_top
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | m1_pre_topc(sK0,X1_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X1_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3515])).

cnf(c_3528,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_3516])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X0)
    | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_741,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X0_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52)
    | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1335,plain,
    ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
    | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2775,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(X0_54,sK0) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1335])).

cnf(c_31,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_32,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_33,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_29,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3352,plain,
    ( m1_pre_topc(X0_54,sK0) != iProver_top
    | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2775,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43])).

cnf(c_3353,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
    | m1_pre_topc(X0_54,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3352])).

cnf(c_3360,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(superposition,[status(thm)],[c_1348,c_3353])).

cnf(c_3562,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3528,c_3360])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_16,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_46,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_48,plain,
    ( m1_pre_topc(sK0,sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_7538,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_32,c_33,c_34,c_41,c_48])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_725,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1350,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_725])).

cnf(c_3529,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_3516])).

cnf(c_3361,plain,
    ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(superposition,[status(thm)],[c_1350,c_3353])).

cnf(c_3549,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK0,sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3529,c_3361])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7244,plain,
    ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3549,c_32,c_33,c_34,c_39,c_48])).

cnf(c_21,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_728,negated_conjecture,
    ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_15,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
    | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_733,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52)))
    | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
    | ~ m1_pre_topc(X2_54,X0_54)
    | ~ m1_pre_topc(X1_54,X0_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X0_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X0_54)
    | ~ l1_pre_topc(X3_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1343,plain,
    ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52))) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)) != iProver_top
    | m1_pre_topc(X2_54,X0_54) != iProver_top
    | m1_pre_topc(X1_54,X0_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_733])).

cnf(c_3258,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1343])).

cnf(c_3261,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3258,c_728])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3338,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3261,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_3339,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3338])).

cnf(c_7284,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7244,c_3339])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7388,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7284,c_35,c_36,c_37,c_42,c_43,c_44])).

cnf(c_7542,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7538,c_7388])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_739,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1337,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)))) = iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_3819,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1337])).

cnf(c_4218,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3819,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_4219,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4218])).

cnf(c_1,plain,
    ( ~ r2_funct_2(X0,X1,X2,X3)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | X2 = X3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_744,plain,
    ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
    | ~ v1_funct_2(X1_52,X0_53,X1_53)
    | ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | X0_52 = X1_52 ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1332,plain,
    ( X0_52 = X1_52
    | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_2269,plain,
    ( sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_1332])).

cnf(c_2650,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2269,c_42,c_43])).

cnf(c_2651,plain,
    ( sK4 = X0_52
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_2650])).

cnf(c_4241,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4219,c_2651])).

cnf(c_4908,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4241,c_35,c_36,c_37])).

cnf(c_4909,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
    | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4908])).

cnf(c_8275,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7542,c_4909])).

cnf(c_2,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_86,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_88,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | l1_struct_0(sK0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_86])).

cnf(c_743,plain,
    ( ~ l1_pre_topc(X0_54)
    | l1_struct_0(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2059,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_2060,plain,
    ( l1_pre_topc(sK1) != iProver_top
    | l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2059])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_737,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52)
    | v1_funct_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1828,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X1_54),u1_struct_0(X1_54),u1_struct_0(sK1))
    | ~ m1_pre_topc(X0_54,X2_54)
    | ~ m1_pre_topc(X1_54,X2_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK1))))
    | ~ v2_pre_topc(X2_54)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(X1_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X2_54)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k10_tmap_1(X2_54,sK1,X1_54,X0_54,k2_tmap_1(sK0,sK1,sK4,X1_54),X0_52))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X1_54)) ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_2440,plain,
    ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_2441,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2440])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_742,plain,
    ( ~ m1_pre_topc(X0_54,X1_54)
    | ~ l1_pre_topc(X1_54)
    | l1_pre_topc(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1334,plain,
    ( m1_pre_topc(X0_54,X1_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | l1_pre_topc(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2356,plain,
    ( l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1348,c_1334])).

cnf(c_2487,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2356,c_34])).

cnf(c_1333,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | l1_struct_0(X0_54) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_2492,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2487,c_1333])).

cnf(c_2357,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1350,c_1334])).

cnf(c_2557,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2357,c_34])).

cnf(c_2562,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2557,c_1333])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_734,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X2_54)
    | ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1764,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_54))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_2745,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_2746,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2745])).

cnf(c_4742,plain,
    ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1764])).

cnf(c_4743,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4742])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X3)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_735,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(X1_54)
    | ~ l1_struct_0(X2_54)
    | ~ v1_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1769,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_54)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_6226,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_6227,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6226])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
    | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
    | ~ m1_pre_topc(X4,X5)
    | ~ m1_pre_topc(X1,X5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X5)
    | v2_struct_0(X5)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X5)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_738,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
    | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))
    | ~ m1_pre_topc(X2_54,X3_54)
    | ~ m1_pre_topc(X0_54,X3_54)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
    | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
    | ~ v2_pre_topc(X3_54)
    | ~ v2_pre_topc(X1_54)
    | v2_struct_0(X0_54)
    | v2_struct_0(X3_54)
    | v2_struct_0(X2_54)
    | v2_struct_0(X1_54)
    | ~ l1_pre_topc(X3_54)
    | ~ l1_pre_topc(X1_54)
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(X1_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1338,plain,
    ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)) = iProver_top
    | m1_pre_topc(X2_54,X3_54) != iProver_top
    | m1_pre_topc(X0_54,X3_54) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
    | v2_pre_topc(X3_54) != iProver_top
    | v2_pre_topc(X1_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(X3_54) = iProver_top
    | v2_struct_0(X2_54) = iProver_top
    | v2_struct_0(X1_54) = iProver_top
    | l1_pre_topc(X3_54) != iProver_top
    | l1_pre_topc(X1_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_4664,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(sK0) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(superposition,[status(thm)],[c_728,c_1338])).

cnf(c_4669,plain,
    ( l1_pre_topc(X0_54) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | v1_funct_1(X1_52) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4664,c_32,c_33,c_34,c_38,c_39,c_40,c_41])).

cnf(c_4670,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
    | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
    | v2_pre_topc(X0_54) != iProver_top
    | v2_struct_0(X0_54) = iProver_top
    | l1_pre_topc(X0_54) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(X1_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_4669])).

cnf(c_4924,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3339,c_4909])).

cnf(c_6265,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4924,c_35,c_36,c_37,c_42,c_43,c_44])).

cnf(c_6266,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6265])).

cnf(c_6278,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v2_pre_topc(sK1) != iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4670,c_6266])).

cnf(c_6281,plain,
    ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6278,c_35,c_36,c_37])).

cnf(c_6282,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6281])).

cnf(c_7247,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7244,c_6282])).

cnf(c_7395,plain,
    ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7247,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2562,c_4743])).

cnf(c_7396,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
    | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
    | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7395])).

cnf(c_7541,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7538,c_7396])).

cnf(c_8411,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8275,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_88,c_2060,c_2441,c_2492,c_2562,c_2746,c_4743,c_6227,c_7541])).

cnf(c_8412,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8411])).

cnf(c_8419,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_8412])).

cnf(c_8885,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1769])).

cnf(c_8886,plain,
    ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8885])).

cnf(c_9364,plain,
    ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8419,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2492,c_2562,c_8886])).

cnf(c_9365,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_9364])).

cnf(c_9370,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK2) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1340,c_9365])).

cnf(c_9515,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9370,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2562])).

cnf(c_4,plain,
    ( v2_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5,plain,
    ( r1_funct_2(X0,X1,X2,X3,X4,X4)
    | ~ v1_funct_2(X4,X2,X3)
    | ~ v1_funct_2(X4,X0,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_17,negated_conjecture,
    ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_337,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X3,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ v1_funct_1(X0)
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != X3
    | u1_struct_0(sK1) != X4
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_338,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_370,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | u1_struct_0(X0) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_338])).

cnf(c_717,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_struct_0(X0_54)
    | ~ l1_struct_0(X0_54)
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_747,plain,
    ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
    | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
    | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | sP0_iProver_split
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_717])).

cnf(c_1358,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_1654,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1358,c_728])).

cnf(c_762,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(X1_52)
    | X1_52 != X0_52 ),
    theory(equality)).

cnf(c_1738,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52 ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_1739,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1738])).

cnf(c_1741,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_2051,plain,
    ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | sP0_iProver_split = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_42,c_1741])).

cnf(c_2052,plain,
    ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
    | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(renaming,[status(thm)],[c_2051])).

cnf(c_9519,plain,
    ( sK4 != sK4
    | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(demodulation,[status(thm)],[c_9515,c_2052])).

cnf(c_9520,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9519])).

cnf(c_746,plain,
    ( v2_struct_0(X0_54)
    | ~ l1_struct_0(X0_54)
    | u1_struct_0(X0_54) != u1_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_717])).

cnf(c_1359,plain,
    ( u1_struct_0(X0_54) != u1_struct_0(sK1)
    | v2_struct_0(X0_54) = iProver_top
    | l1_struct_0(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_2138,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1359])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9520,c_2138,c_2060,c_44,c_43,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.96/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.96/0.99  
% 3.96/0.99  ------  iProver source info
% 3.96/0.99  
% 3.96/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.96/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.96/0.99  git: non_committed_changes: false
% 3.96/0.99  git: last_make_outside_of_git: false
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options
% 3.96/0.99  
% 3.96/0.99  --out_options                           all
% 3.96/0.99  --tptp_safe_out                         true
% 3.96/0.99  --problem_path                          ""
% 3.96/0.99  --include_path                          ""
% 3.96/0.99  --clausifier                            res/vclausify_rel
% 3.96/0.99  --clausifier_options                    --mode clausify
% 3.96/0.99  --stdin                                 false
% 3.96/0.99  --stats_out                             all
% 3.96/0.99  
% 3.96/0.99  ------ General Options
% 3.96/0.99  
% 3.96/0.99  --fof                                   false
% 3.96/0.99  --time_out_real                         305.
% 3.96/0.99  --time_out_virtual                      -1.
% 3.96/0.99  --symbol_type_check                     false
% 3.96/0.99  --clausify_out                          false
% 3.96/0.99  --sig_cnt_out                           false
% 3.96/0.99  --trig_cnt_out                          false
% 3.96/0.99  --trig_cnt_out_tolerance                1.
% 3.96/0.99  --trig_cnt_out_sk_spl                   false
% 3.96/0.99  --abstr_cl_out                          false
% 3.96/0.99  
% 3.96/0.99  ------ Global Options
% 3.96/0.99  
% 3.96/0.99  --schedule                              default
% 3.96/0.99  --add_important_lit                     false
% 3.96/0.99  --prop_solver_per_cl                    1000
% 3.96/0.99  --min_unsat_core                        false
% 3.96/0.99  --soft_assumptions                      false
% 3.96/0.99  --soft_lemma_size                       3
% 3.96/0.99  --prop_impl_unit_size                   0
% 3.96/0.99  --prop_impl_unit                        []
% 3.96/0.99  --share_sel_clauses                     true
% 3.96/0.99  --reset_solvers                         false
% 3.96/0.99  --bc_imp_inh                            [conj_cone]
% 3.96/0.99  --conj_cone_tolerance                   3.
% 3.96/0.99  --extra_neg_conj                        none
% 3.96/0.99  --large_theory_mode                     true
% 3.96/0.99  --prolific_symb_bound                   200
% 3.96/0.99  --lt_threshold                          2000
% 3.96/0.99  --clause_weak_htbl                      true
% 3.96/0.99  --gc_record_bc_elim                     false
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing Options
% 3.96/0.99  
% 3.96/0.99  --preprocessing_flag                    true
% 3.96/0.99  --time_out_prep_mult                    0.1
% 3.96/0.99  --splitting_mode                        input
% 3.96/0.99  --splitting_grd                         true
% 3.96/0.99  --splitting_cvd                         false
% 3.96/0.99  --splitting_cvd_svl                     false
% 3.96/0.99  --splitting_nvd                         32
% 3.96/0.99  --sub_typing                            true
% 3.96/0.99  --prep_gs_sim                           true
% 3.96/0.99  --prep_unflatten                        true
% 3.96/0.99  --prep_res_sim                          true
% 3.96/0.99  --prep_upred                            true
% 3.96/0.99  --prep_sem_filter                       exhaustive
% 3.96/0.99  --prep_sem_filter_out                   false
% 3.96/0.99  --pred_elim                             true
% 3.96/0.99  --res_sim_input                         true
% 3.96/0.99  --eq_ax_congr_red                       true
% 3.96/0.99  --pure_diseq_elim                       true
% 3.96/0.99  --brand_transform                       false
% 3.96/0.99  --non_eq_to_eq                          false
% 3.96/0.99  --prep_def_merge                        true
% 3.96/0.99  --prep_def_merge_prop_impl              false
% 3.96/0.99  --prep_def_merge_mbd                    true
% 3.96/0.99  --prep_def_merge_tr_red                 false
% 3.96/0.99  --prep_def_merge_tr_cl                  false
% 3.96/0.99  --smt_preprocessing                     true
% 3.96/0.99  --smt_ac_axioms                         fast
% 3.96/0.99  --preprocessed_out                      false
% 3.96/0.99  --preprocessed_stats                    false
% 3.96/0.99  
% 3.96/0.99  ------ Abstraction refinement Options
% 3.96/0.99  
% 3.96/0.99  --abstr_ref                             []
% 3.96/0.99  --abstr_ref_prep                        false
% 3.96/0.99  --abstr_ref_until_sat                   false
% 3.96/0.99  --abstr_ref_sig_restrict                funpre
% 3.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.99  --abstr_ref_under                       []
% 3.96/0.99  
% 3.96/0.99  ------ SAT Options
% 3.96/0.99  
% 3.96/0.99  --sat_mode                              false
% 3.96/0.99  --sat_fm_restart_options                ""
% 3.96/0.99  --sat_gr_def                            false
% 3.96/0.99  --sat_epr_types                         true
% 3.96/0.99  --sat_non_cyclic_types                  false
% 3.96/0.99  --sat_finite_models                     false
% 3.96/0.99  --sat_fm_lemmas                         false
% 3.96/0.99  --sat_fm_prep                           false
% 3.96/0.99  --sat_fm_uc_incr                        true
% 3.96/0.99  --sat_out_model                         small
% 3.96/0.99  --sat_out_clauses                       false
% 3.96/0.99  
% 3.96/0.99  ------ QBF Options
% 3.96/0.99  
% 3.96/0.99  --qbf_mode                              false
% 3.96/0.99  --qbf_elim_univ                         false
% 3.96/0.99  --qbf_dom_inst                          none
% 3.96/0.99  --qbf_dom_pre_inst                      false
% 3.96/0.99  --qbf_sk_in                             false
% 3.96/0.99  --qbf_pred_elim                         true
% 3.96/0.99  --qbf_split                             512
% 3.96/0.99  
% 3.96/0.99  ------ BMC1 Options
% 3.96/0.99  
% 3.96/0.99  --bmc1_incremental                      false
% 3.96/0.99  --bmc1_axioms                           reachable_all
% 3.96/0.99  --bmc1_min_bound                        0
% 3.96/0.99  --bmc1_max_bound                        -1
% 3.96/0.99  --bmc1_max_bound_default                -1
% 3.96/0.99  --bmc1_symbol_reachability              true
% 3.96/0.99  --bmc1_property_lemmas                  false
% 3.96/0.99  --bmc1_k_induction                      false
% 3.96/0.99  --bmc1_non_equiv_states                 false
% 3.96/0.99  --bmc1_deadlock                         false
% 3.96/0.99  --bmc1_ucm                              false
% 3.96/0.99  --bmc1_add_unsat_core                   none
% 3.96/0.99  --bmc1_unsat_core_children              false
% 3.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.99  --bmc1_out_stat                         full
% 3.96/0.99  --bmc1_ground_init                      false
% 3.96/0.99  --bmc1_pre_inst_next_state              false
% 3.96/0.99  --bmc1_pre_inst_state                   false
% 3.96/0.99  --bmc1_pre_inst_reach_state             false
% 3.96/0.99  --bmc1_out_unsat_core                   false
% 3.96/0.99  --bmc1_aig_witness_out                  false
% 3.96/0.99  --bmc1_verbose                          false
% 3.96/0.99  --bmc1_dump_clauses_tptp                false
% 3.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.99  --bmc1_dump_file                        -
% 3.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.99  --bmc1_ucm_extend_mode                  1
% 3.96/0.99  --bmc1_ucm_init_mode                    2
% 3.96/0.99  --bmc1_ucm_cone_mode                    none
% 3.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.99  --bmc1_ucm_relax_model                  4
% 3.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.99  --bmc1_ucm_layered_model                none
% 3.96/0.99  --bmc1_ucm_max_lemma_size               10
% 3.96/0.99  
% 3.96/0.99  ------ AIG Options
% 3.96/0.99  
% 3.96/0.99  --aig_mode                              false
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation Options
% 3.96/0.99  
% 3.96/0.99  --instantiation_flag                    true
% 3.96/0.99  --inst_sos_flag                         false
% 3.96/0.99  --inst_sos_phase                        true
% 3.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel_side                     num_symb
% 3.96/0.99  --inst_solver_per_active                1400
% 3.96/0.99  --inst_solver_calls_frac                1.
% 3.96/0.99  --inst_passive_queue_type               priority_queues
% 3.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.99  --inst_passive_queues_freq              [25;2]
% 3.96/0.99  --inst_dismatching                      true
% 3.96/0.99  --inst_eager_unprocessed_to_passive     true
% 3.96/0.99  --inst_prop_sim_given                   true
% 3.96/0.99  --inst_prop_sim_new                     false
% 3.96/0.99  --inst_subs_new                         false
% 3.96/0.99  --inst_eq_res_simp                      false
% 3.96/0.99  --inst_subs_given                       false
% 3.96/0.99  --inst_orphan_elimination               true
% 3.96/0.99  --inst_learning_loop_flag               true
% 3.96/0.99  --inst_learning_start                   3000
% 3.96/0.99  --inst_learning_factor                  2
% 3.96/0.99  --inst_start_prop_sim_after_learn       3
% 3.96/0.99  --inst_sel_renew                        solver
% 3.96/0.99  --inst_lit_activity_flag                true
% 3.96/0.99  --inst_restr_to_given                   false
% 3.96/0.99  --inst_activity_threshold               500
% 3.96/0.99  --inst_out_proof                        true
% 3.96/0.99  
% 3.96/0.99  ------ Resolution Options
% 3.96/0.99  
% 3.96/0.99  --resolution_flag                       true
% 3.96/0.99  --res_lit_sel                           adaptive
% 3.96/0.99  --res_lit_sel_side                      none
% 3.96/0.99  --res_ordering                          kbo
% 3.96/0.99  --res_to_prop_solver                    active
% 3.96/0.99  --res_prop_simpl_new                    false
% 3.96/0.99  --res_prop_simpl_given                  true
% 3.96/0.99  --res_passive_queue_type                priority_queues
% 3.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.99  --res_passive_queues_freq               [15;5]
% 3.96/0.99  --res_forward_subs                      full
% 3.96/0.99  --res_backward_subs                     full
% 3.96/0.99  --res_forward_subs_resolution           true
% 3.96/0.99  --res_backward_subs_resolution          true
% 3.96/0.99  --res_orphan_elimination                true
% 3.96/0.99  --res_time_limit                        2.
% 3.96/0.99  --res_out_proof                         true
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Options
% 3.96/0.99  
% 3.96/0.99  --superposition_flag                    true
% 3.96/0.99  --sup_passive_queue_type                priority_queues
% 3.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.99  --demod_completeness_check              fast
% 3.96/0.99  --demod_use_ground                      true
% 3.96/0.99  --sup_to_prop_solver                    passive
% 3.96/0.99  --sup_prop_simpl_new                    true
% 3.96/0.99  --sup_prop_simpl_given                  true
% 3.96/0.99  --sup_fun_splitting                     false
% 3.96/0.99  --sup_smt_interval                      50000
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Simplification Setup
% 3.96/0.99  
% 3.96/0.99  --sup_indices_passive                   []
% 3.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_full_bw                           [BwDemod]
% 3.96/0.99  --sup_immed_triv                        [TrivRules]
% 3.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_immed_bw_main                     []
% 3.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.99  
% 3.96/0.99  ------ Combination Options
% 3.96/0.99  
% 3.96/0.99  --comb_res_mult                         3
% 3.96/0.99  --comb_sup_mult                         2
% 3.96/0.99  --comb_inst_mult                        10
% 3.96/0.99  
% 3.96/0.99  ------ Debug Options
% 3.96/0.99  
% 3.96/0.99  --dbg_backtrace                         false
% 3.96/0.99  --dbg_dump_prop_clauses                 false
% 3.96/0.99  --dbg_dump_prop_clauses_file            -
% 3.96/0.99  --dbg_out_stat                          false
% 3.96/0.99  ------ Parsing...
% 3.96/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.96/0.99  ------ Proving...
% 3.96/0.99  ------ Problem Properties 
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  clauses                                 30
% 3.96/0.99  conjectures                             14
% 3.96/0.99  EPR                                     14
% 3.96/0.99  Horn                                    24
% 3.96/0.99  unary                                   14
% 3.96/0.99  binary                                  2
% 3.96/0.99  lits                                    154
% 3.96/0.99  lits eq                                 6
% 3.96/0.99  fd_pure                                 0
% 3.96/0.99  fd_pseudo                               0
% 3.96/0.99  fd_cond                                 0
% 3.96/0.99  fd_pseudo_cond                          1
% 3.96/0.99  AC symbols                              0
% 3.96/0.99  
% 3.96/0.99  ------ Schedule dynamic 5 is on 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ 
% 3.96/0.99  Current options:
% 3.96/0.99  ------ 
% 3.96/0.99  
% 3.96/0.99  ------ Input Options
% 3.96/0.99  
% 3.96/0.99  --out_options                           all
% 3.96/0.99  --tptp_safe_out                         true
% 3.96/0.99  --problem_path                          ""
% 3.96/0.99  --include_path                          ""
% 3.96/0.99  --clausifier                            res/vclausify_rel
% 3.96/0.99  --clausifier_options                    --mode clausify
% 3.96/0.99  --stdin                                 false
% 3.96/0.99  --stats_out                             all
% 3.96/0.99  
% 3.96/0.99  ------ General Options
% 3.96/0.99  
% 3.96/0.99  --fof                                   false
% 3.96/0.99  --time_out_real                         305.
% 3.96/0.99  --time_out_virtual                      -1.
% 3.96/0.99  --symbol_type_check                     false
% 3.96/0.99  --clausify_out                          false
% 3.96/0.99  --sig_cnt_out                           false
% 3.96/0.99  --trig_cnt_out                          false
% 3.96/0.99  --trig_cnt_out_tolerance                1.
% 3.96/0.99  --trig_cnt_out_sk_spl                   false
% 3.96/0.99  --abstr_cl_out                          false
% 3.96/0.99  
% 3.96/0.99  ------ Global Options
% 3.96/0.99  
% 3.96/0.99  --schedule                              default
% 3.96/0.99  --add_important_lit                     false
% 3.96/0.99  --prop_solver_per_cl                    1000
% 3.96/0.99  --min_unsat_core                        false
% 3.96/0.99  --soft_assumptions                      false
% 3.96/0.99  --soft_lemma_size                       3
% 3.96/0.99  --prop_impl_unit_size                   0
% 3.96/0.99  --prop_impl_unit                        []
% 3.96/0.99  --share_sel_clauses                     true
% 3.96/0.99  --reset_solvers                         false
% 3.96/0.99  --bc_imp_inh                            [conj_cone]
% 3.96/0.99  --conj_cone_tolerance                   3.
% 3.96/0.99  --extra_neg_conj                        none
% 3.96/0.99  --large_theory_mode                     true
% 3.96/0.99  --prolific_symb_bound                   200
% 3.96/0.99  --lt_threshold                          2000
% 3.96/0.99  --clause_weak_htbl                      true
% 3.96/0.99  --gc_record_bc_elim                     false
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing Options
% 3.96/0.99  
% 3.96/0.99  --preprocessing_flag                    true
% 3.96/0.99  --time_out_prep_mult                    0.1
% 3.96/0.99  --splitting_mode                        input
% 3.96/0.99  --splitting_grd                         true
% 3.96/0.99  --splitting_cvd                         false
% 3.96/0.99  --splitting_cvd_svl                     false
% 3.96/0.99  --splitting_nvd                         32
% 3.96/0.99  --sub_typing                            true
% 3.96/0.99  --prep_gs_sim                           true
% 3.96/0.99  --prep_unflatten                        true
% 3.96/0.99  --prep_res_sim                          true
% 3.96/0.99  --prep_upred                            true
% 3.96/0.99  --prep_sem_filter                       exhaustive
% 3.96/0.99  --prep_sem_filter_out                   false
% 3.96/0.99  --pred_elim                             true
% 3.96/0.99  --res_sim_input                         true
% 3.96/0.99  --eq_ax_congr_red                       true
% 3.96/0.99  --pure_diseq_elim                       true
% 3.96/0.99  --brand_transform                       false
% 3.96/0.99  --non_eq_to_eq                          false
% 3.96/0.99  --prep_def_merge                        true
% 3.96/0.99  --prep_def_merge_prop_impl              false
% 3.96/0.99  --prep_def_merge_mbd                    true
% 3.96/0.99  --prep_def_merge_tr_red                 false
% 3.96/0.99  --prep_def_merge_tr_cl                  false
% 3.96/0.99  --smt_preprocessing                     true
% 3.96/0.99  --smt_ac_axioms                         fast
% 3.96/0.99  --preprocessed_out                      false
% 3.96/0.99  --preprocessed_stats                    false
% 3.96/0.99  
% 3.96/0.99  ------ Abstraction refinement Options
% 3.96/0.99  
% 3.96/0.99  --abstr_ref                             []
% 3.96/0.99  --abstr_ref_prep                        false
% 3.96/0.99  --abstr_ref_until_sat                   false
% 3.96/0.99  --abstr_ref_sig_restrict                funpre
% 3.96/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.96/0.99  --abstr_ref_under                       []
% 3.96/0.99  
% 3.96/0.99  ------ SAT Options
% 3.96/0.99  
% 3.96/0.99  --sat_mode                              false
% 3.96/0.99  --sat_fm_restart_options                ""
% 3.96/0.99  --sat_gr_def                            false
% 3.96/0.99  --sat_epr_types                         true
% 3.96/0.99  --sat_non_cyclic_types                  false
% 3.96/0.99  --sat_finite_models                     false
% 3.96/0.99  --sat_fm_lemmas                         false
% 3.96/0.99  --sat_fm_prep                           false
% 3.96/0.99  --sat_fm_uc_incr                        true
% 3.96/0.99  --sat_out_model                         small
% 3.96/0.99  --sat_out_clauses                       false
% 3.96/0.99  
% 3.96/0.99  ------ QBF Options
% 3.96/0.99  
% 3.96/0.99  --qbf_mode                              false
% 3.96/0.99  --qbf_elim_univ                         false
% 3.96/0.99  --qbf_dom_inst                          none
% 3.96/0.99  --qbf_dom_pre_inst                      false
% 3.96/0.99  --qbf_sk_in                             false
% 3.96/0.99  --qbf_pred_elim                         true
% 3.96/0.99  --qbf_split                             512
% 3.96/0.99  
% 3.96/0.99  ------ BMC1 Options
% 3.96/0.99  
% 3.96/0.99  --bmc1_incremental                      false
% 3.96/0.99  --bmc1_axioms                           reachable_all
% 3.96/0.99  --bmc1_min_bound                        0
% 3.96/0.99  --bmc1_max_bound                        -1
% 3.96/0.99  --bmc1_max_bound_default                -1
% 3.96/0.99  --bmc1_symbol_reachability              true
% 3.96/0.99  --bmc1_property_lemmas                  false
% 3.96/0.99  --bmc1_k_induction                      false
% 3.96/0.99  --bmc1_non_equiv_states                 false
% 3.96/0.99  --bmc1_deadlock                         false
% 3.96/0.99  --bmc1_ucm                              false
% 3.96/0.99  --bmc1_add_unsat_core                   none
% 3.96/0.99  --bmc1_unsat_core_children              false
% 3.96/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.96/0.99  --bmc1_out_stat                         full
% 3.96/0.99  --bmc1_ground_init                      false
% 3.96/0.99  --bmc1_pre_inst_next_state              false
% 3.96/0.99  --bmc1_pre_inst_state                   false
% 3.96/0.99  --bmc1_pre_inst_reach_state             false
% 3.96/0.99  --bmc1_out_unsat_core                   false
% 3.96/0.99  --bmc1_aig_witness_out                  false
% 3.96/0.99  --bmc1_verbose                          false
% 3.96/0.99  --bmc1_dump_clauses_tptp                false
% 3.96/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.96/0.99  --bmc1_dump_file                        -
% 3.96/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.96/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.96/0.99  --bmc1_ucm_extend_mode                  1
% 3.96/0.99  --bmc1_ucm_init_mode                    2
% 3.96/0.99  --bmc1_ucm_cone_mode                    none
% 3.96/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.96/0.99  --bmc1_ucm_relax_model                  4
% 3.96/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.96/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.96/0.99  --bmc1_ucm_layered_model                none
% 3.96/0.99  --bmc1_ucm_max_lemma_size               10
% 3.96/0.99  
% 3.96/0.99  ------ AIG Options
% 3.96/0.99  
% 3.96/0.99  --aig_mode                              false
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation Options
% 3.96/0.99  
% 3.96/0.99  --instantiation_flag                    true
% 3.96/0.99  --inst_sos_flag                         false
% 3.96/0.99  --inst_sos_phase                        true
% 3.96/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.96/0.99  --inst_lit_sel_side                     none
% 3.96/0.99  --inst_solver_per_active                1400
% 3.96/0.99  --inst_solver_calls_frac                1.
% 3.96/0.99  --inst_passive_queue_type               priority_queues
% 3.96/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.96/0.99  --inst_passive_queues_freq              [25;2]
% 3.96/0.99  --inst_dismatching                      true
% 3.96/0.99  --inst_eager_unprocessed_to_passive     true
% 3.96/0.99  --inst_prop_sim_given                   true
% 3.96/0.99  --inst_prop_sim_new                     false
% 3.96/0.99  --inst_subs_new                         false
% 3.96/0.99  --inst_eq_res_simp                      false
% 3.96/0.99  --inst_subs_given                       false
% 3.96/0.99  --inst_orphan_elimination               true
% 3.96/0.99  --inst_learning_loop_flag               true
% 3.96/0.99  --inst_learning_start                   3000
% 3.96/0.99  --inst_learning_factor                  2
% 3.96/0.99  --inst_start_prop_sim_after_learn       3
% 3.96/0.99  --inst_sel_renew                        solver
% 3.96/0.99  --inst_lit_activity_flag                true
% 3.96/0.99  --inst_restr_to_given                   false
% 3.96/0.99  --inst_activity_threshold               500
% 3.96/0.99  --inst_out_proof                        true
% 3.96/0.99  
% 3.96/0.99  ------ Resolution Options
% 3.96/0.99  
% 3.96/0.99  --resolution_flag                       false
% 3.96/0.99  --res_lit_sel                           adaptive
% 3.96/0.99  --res_lit_sel_side                      none
% 3.96/0.99  --res_ordering                          kbo
% 3.96/0.99  --res_to_prop_solver                    active
% 3.96/0.99  --res_prop_simpl_new                    false
% 3.96/0.99  --res_prop_simpl_given                  true
% 3.96/0.99  --res_passive_queue_type                priority_queues
% 3.96/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.96/0.99  --res_passive_queues_freq               [15;5]
% 3.96/0.99  --res_forward_subs                      full
% 3.96/0.99  --res_backward_subs                     full
% 3.96/0.99  --res_forward_subs_resolution           true
% 3.96/0.99  --res_backward_subs_resolution          true
% 3.96/0.99  --res_orphan_elimination                true
% 3.96/0.99  --res_time_limit                        2.
% 3.96/0.99  --res_out_proof                         true
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Options
% 3.96/0.99  
% 3.96/0.99  --superposition_flag                    true
% 3.96/0.99  --sup_passive_queue_type                priority_queues
% 3.96/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.96/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.96/0.99  --demod_completeness_check              fast
% 3.96/0.99  --demod_use_ground                      true
% 3.96/0.99  --sup_to_prop_solver                    passive
% 3.96/0.99  --sup_prop_simpl_new                    true
% 3.96/0.99  --sup_prop_simpl_given                  true
% 3.96/0.99  --sup_fun_splitting                     false
% 3.96/0.99  --sup_smt_interval                      50000
% 3.96/0.99  
% 3.96/0.99  ------ Superposition Simplification Setup
% 3.96/0.99  
% 3.96/0.99  --sup_indices_passive                   []
% 3.96/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.96/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.96/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_full_bw                           [BwDemod]
% 3.96/0.99  --sup_immed_triv                        [TrivRules]
% 3.96/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.96/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_immed_bw_main                     []
% 3.96/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.96/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.96/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.96/0.99  
% 3.96/0.99  ------ Combination Options
% 3.96/0.99  
% 3.96/0.99  --comb_res_mult                         3
% 3.96/0.99  --comb_sup_mult                         2
% 3.96/0.99  --comb_inst_mult                        10
% 3.96/0.99  
% 3.96/0.99  ------ Debug Options
% 3.96/0.99  
% 3.96/0.99  --dbg_backtrace                         false
% 3.96/0.99  --dbg_dump_prop_clauses                 false
% 3.96/0.99  --dbg_dump_prop_clauses_file            -
% 3.96/0.99  --dbg_out_stat                          false
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  ------ Proving...
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS status Theorem for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  fof(f9,axiom,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((l1_struct_0(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2) & l1_struct_0(X1) & l1_struct_0(X0)) => (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f28,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | (~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f9])).
% 3.96/0.99  
% 3.96/0.99  fof(f29,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(k2_tmap_1(X0,X1,X2,X3))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f28])).
% 3.96/0.99  
% 3.96/0.99  fof(f57,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_tmap_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f29])).
% 3.96/0.99  
% 3.96/0.99  fof(f12,conjecture,(
% 3.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f13,negated_conjecture,(
% 3.96/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X2,X3) = X0 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3)))))))))),
% 3.96/0.99    inference(negated_conjecture,[],[f12])).
% 3.96/0.99  
% 3.96/0.99  fof(f33,plain,(
% 3.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4))) & k1_tsep_1(X0,X2,X3) = X0) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f13])).
% 3.96/0.99  
% 3.96/0.99  fof(f34,plain,(
% 3.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f33])).
% 3.96/0.99  
% 3.96/0.99  fof(f41,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) => (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),sK4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,sK4,X2),k2_tmap_1(X0,X1,sK4,X3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f40,plain,(
% 3.96/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,sK3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,sK3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,sK3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,sK3) = X0 & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f39,plain,(
% 3.96/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,sK2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,sK2,X3,k2_tmap_1(X0,X1,X4,sK2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,sK2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f38,plain,(
% 3.96/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(sK1),X4,k10_tmap_1(X0,sK1,X2,X3,k2_tmap_1(X0,sK1,X4,X2),k2_tmap_1(X0,sK1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))) )),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f37,plain,(
% 3.96/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k2_tmap_1(X0,X1,X4,X2),k2_tmap_1(X0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(X0,X2,X3) = X0 & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~r1_funct_2(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(k1_tsep_1(sK0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(sK0,X1,X2,X3,k2_tmap_1(sK0,X1,X4,X2),k2_tmap_1(sK0,X1,X4,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X4)) & k1_tsep_1(sK0,X2,X3) = sK0 & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.96/0.99    introduced(choice_axiom,[])).
% 3.96/0.99  
% 3.96/0.99  fof(f42,plain,(
% 3.96/0.99    ((((~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK4)) & k1_tsep_1(sK0,sK2,sK3) = sK0 & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.96/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f34,f41,f40,f39,f38,f37])).
% 3.96/0.99  
% 3.96/0.99  fof(f69,plain,(
% 3.96/0.99    m1_pre_topc(sK3,sK0)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f73,plain,(
% 3.96/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f7,axiom,(
% 3.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4)))))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f24,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f7])).
% 3.96/0.99  
% 3.96/0.99  fof(f25,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f24])).
% 3.96/0.99  
% 3.96/0.99  fof(f51,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) = k3_tmap_1(X0,X1,X2,X3,X4) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f25])).
% 3.96/0.99  
% 3.96/0.99  fof(f63,plain,(
% 3.96/0.99    ~v2_struct_0(sK1)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f64,plain,(
% 3.96/0.99    v2_pre_topc(sK1)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f65,plain,(
% 3.96/0.99    l1_pre_topc(sK1)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f71,plain,(
% 3.96/0.99    v1_funct_1(sK4)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f72,plain,(
% 3.96/0.99    v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f6,axiom,(
% 3.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_pre_topc(X3,X0) => k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3))))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f22,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f6])).
% 3.96/0.99  
% 3.96/0.99  fof(f23,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f22])).
% 3.96/0.99  
% 3.96/0.99  fof(f50,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (k2_tmap_1(X0,X1,X2,X3) = k2_partfun1(u1_struct_0(X0),u1_struct_0(X1),X2,u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f23])).
% 3.96/0.99  
% 3.96/0.99  fof(f60,plain,(
% 3.96/0.99    ~v2_struct_0(sK0)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f61,plain,(
% 3.96/0.99    v2_pre_topc(sK0)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f62,plain,(
% 3.96/0.99    l1_pre_topc(sK0)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f11,axiom,(
% 3.96/0.99    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f32,plain,(
% 3.96/0.99    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.96/0.99    inference(ennf_transformation,[],[f11])).
% 3.96/0.99  
% 3.96/0.99  fof(f59,plain,(
% 3.96/0.99    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f32])).
% 3.96/0.99  
% 3.96/0.99  fof(f67,plain,(
% 3.96/0.99    m1_pre_topc(sK2,sK0)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f70,plain,(
% 3.96/0.99    k1_tsep_1(sK0,sK2,sK3) = sK0),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f10,axiom,(
% 3.96/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(X4)) => r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))))))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f30,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f10])).
% 3.96/0.99  
% 3.96/0.99  fof(f31,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f30])).
% 3.96/0.99  
% 3.96/0.99  fof(f58,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X3,X1] : (r2_funct_2(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1),X4,k10_tmap_1(X0,X1,X2,X3,k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X2,X4),k3_tmap_1(X0,X1,k1_tsep_1(X0,X2,X3),X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f31])).
% 3.96/0.99  
% 3.96/0.99  fof(f66,plain,(
% 3.96/0.99    ~v2_struct_0(sK2)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f68,plain,(
% 3.96/0.99    ~v2_struct_0(sK3)),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  fof(f8,axiom,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f26,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f8])).
% 3.96/0.99  
% 3.96/0.99  fof(f27,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) & v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) & v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f26])).
% 3.96/0.99  
% 3.96/0.99  fof(f54,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k10_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f27])).
% 3.96/0.99  
% 3.96/0.99  fof(f1,axiom,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f14,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.96/0.99    inference(ennf_transformation,[],[f1])).
% 3.96/0.99  
% 3.96/0.99  fof(f15,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.96/0.99    inference(flattening,[],[f14])).
% 3.96/0.99  
% 3.96/0.99  fof(f35,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.96/0.99    inference(nnf_transformation,[],[f15])).
% 3.96/0.99  
% 3.96/0.99  fof(f43,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f35])).
% 3.96/0.99  
% 3.96/0.99  fof(f2,axiom,(
% 3.96/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f16,plain,(
% 3.96/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.96/0.99    inference(ennf_transformation,[],[f2])).
% 3.96/0.99  
% 3.96/0.99  fof(f45,plain,(
% 3.96/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f16])).
% 3.96/0.99  
% 3.96/0.99  fof(f52,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k10_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f27])).
% 3.96/0.99  
% 3.96/0.99  fof(f3,axiom,(
% 3.96/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f17,plain,(
% 3.96/0.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.96/0.99    inference(ennf_transformation,[],[f3])).
% 3.96/0.99  
% 3.96/0.99  fof(f46,plain,(
% 3.96/0.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f17])).
% 3.96/0.99  
% 3.96/0.99  fof(f55,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_tmap_1(X0,X1,X2,X3)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f29])).
% 3.96/0.99  
% 3.96/0.99  fof(f56,plain,(
% 3.96/0.99    ( ! [X2,X0,X3,X1] : (v1_funct_2(k2_tmap_1(X0,X1,X2,X3),u1_struct_0(X3),u1_struct_0(X1)) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f29])).
% 3.96/0.99  
% 3.96/0.99  fof(f53,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k10_tmap_1(X0,X1,X2,X3,X4,X5),u1_struct_0(k1_tsep_1(X0,X2,X3)),u1_struct_0(X1)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) | ~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1)) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f27])).
% 3.96/0.99  
% 3.96/0.99  fof(f4,axiom,(
% 3.96/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f18,plain,(
% 3.96/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.96/0.99    inference(ennf_transformation,[],[f4])).
% 3.96/0.99  
% 3.96/0.99  fof(f19,plain,(
% 3.96/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.96/0.99    inference(flattening,[],[f18])).
% 3.96/0.99  
% 3.96/0.99  fof(f47,plain,(
% 3.96/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f19])).
% 3.96/0.99  
% 3.96/0.99  fof(f5,axiom,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_2(X5,X2,X3) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4) & ~v1_xboole_0(X3) & ~v1_xboole_0(X1)) => (r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5))),
% 3.96/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.96/0.99  
% 3.96/0.99  fof(f20,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)))),
% 3.96/0.99    inference(ennf_transformation,[],[f5])).
% 3.96/0.99  
% 3.96/0.99  fof(f21,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : ((r1_funct_2(X0,X1,X2,X3,X4,X5) <=> X4 = X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.96/0.99    inference(flattening,[],[f20])).
% 3.96/0.99  
% 3.96/0.99  fof(f36,plain,(
% 3.96/0.99    ! [X0,X1,X2,X3,X4,X5] : (((r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5) & (X4 = X5 | ~r1_funct_2(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1))),
% 3.96/0.99    inference(nnf_transformation,[],[f21])).
% 3.96/0.99  
% 3.96/0.99  fof(f49,plain,(
% 3.96/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X4,X5) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.96/0.99    inference(cnf_transformation,[],[f36])).
% 3.96/0.99  
% 3.96/0.99  fof(f76,plain,(
% 3.96/0.99    ( ! [X2,X0,X5,X3,X1] : (r1_funct_2(X0,X1,X2,X3,X5,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(X5,X2,X3) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X5,X0,X1) | ~v1_funct_1(X5) | v1_xboole_0(X3) | v1_xboole_0(X1)) )),
% 3.96/0.99    inference(equality_resolution,[],[f49])).
% 3.96/0.99  
% 3.96/0.99  fof(f74,plain,(
% 3.96/0.99    ~r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))),
% 3.96/0.99    inference(cnf_transformation,[],[f42])).
% 3.96/0.99  
% 3.96/0.99  cnf(c_12,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | m1_subset_1(k2_tmap_1(X1,X2,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
% 3.96/0.99      | ~ l1_struct_0(X1)
% 3.96/0.99      | ~ l1_struct_0(X3)
% 3.96/0.99      | ~ l1_struct_0(X2)
% 3.96/0.99      | ~ v1_funct_1(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_736,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(X1_54)
% 3.96/0.99      | ~ l1_struct_0(X2_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1340,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) = iProver_top
% 3.96/0.99      | l1_struct_0(X1_54) != iProver_top
% 3.96/0.99      | l1_struct_0(X2_54) != iProver_top
% 3.96/0.99      | l1_struct_0(X0_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_22,negated_conjecture,
% 3.96/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_727,negated_conjecture,
% 3.96/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_22]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1348,plain,
% 3.96/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_18,negated_conjecture,
% 3.96/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.96/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_731,negated_conjecture,
% 3.96/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1345,plain,
% 3.96/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_pre_topc(X3,X4)
% 3.96/0.99      | ~ m1_pre_topc(X3,X1)
% 3.96/0.99      | ~ m1_pre_topc(X1,X4)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ v2_pre_topc(X2)
% 3.96/0.99      | ~ v2_pre_topc(X4)
% 3.96/0.99      | v2_struct_0(X4)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | ~ l1_pre_topc(X4)
% 3.96/0.99      | ~ l1_pre_topc(X2)
% 3.96/0.99      | ~ v1_funct_1(X0)
% 3.96/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k3_tmap_1(X4,X2,X1,X3,X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_740,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X0_54)
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X3_54)
% 3.96/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ v2_pre_topc(X3_54)
% 3.96/0.99      | ~ v2_pre_topc(X1_54)
% 3.96/0.99      | v2_struct_0(X3_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X3_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1336,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k3_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52)
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3021,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,X1_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1345,c_1336]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_28,negated_conjecture,
% 3.96/0.99      ( ~ v2_struct_0(sK1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_35,plain,
% 3.96/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_27,negated_conjecture,
% 3.96/0.99      ( v2_pre_topc(sK1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_36,plain,
% 3.96/0.99      ( v2_pre_topc(sK1) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_26,negated_conjecture,
% 3.96/0.99      ( l1_pre_topc(sK1) ),
% 3.96/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_37,plain,
% 3.96/0.99      ( l1_pre_topc(sK1) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_20,negated_conjecture,
% 3.96/0.99      ( v1_funct_1(sK4) ),
% 3.96/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_42,plain,
% 3.96/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_19,negated_conjecture,
% 3.96/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_43,plain,
% 3.96/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3515,plain,
% 3.96/0.99      ( v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 3.96/0.99      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,X1_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3021,c_35,c_36,c_37,c_42,c_43]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3516,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k3_tmap_1(X1_54,sK1,sK0,X0_54,sK4)
% 3.96/0.99      | m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,X1_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_3515]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3528,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k3_tmap_1(sK0,sK1,sK0,sK3,sK4)
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1348,c_3516]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_pre_topc(X3,X1)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ v2_pre_topc(X2)
% 3.96/0.99      | ~ v2_pre_topc(X1)
% 3.96/0.99      | v2_struct_0(X1)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | ~ l1_pre_topc(X1)
% 3.96/0.99      | ~ l1_pre_topc(X2)
% 3.96/0.99      | ~ v1_funct_1(X0)
% 3.96/0.99      | k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X0,u1_struct_0(X3)) = k2_tmap_1(X1,X2,X0,X3) ),
% 3.96/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_741,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X0_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ v2_pre_topc(X0_54)
% 3.96/0.99      | ~ v2_pre_topc(X1_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X0_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1335,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(X0_54),u1_struct_0(X1_54),X0_52,u1_struct_0(X2_54)) = k2_tmap_1(X0_54,X1_54,X0_52,X2_54)
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2775,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,sK0) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1345,c_1335]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_31,negated_conjecture,
% 3.96/0.99      ( ~ v2_struct_0(sK0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_32,plain,
% 3.96/0.99      ( v2_struct_0(sK0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_30,negated_conjecture,
% 3.96/0.99      ( v2_pre_topc(sK0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_33,plain,
% 3.96/0.99      ( v2_pre_topc(sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_29,negated_conjecture,
% 3.96/0.99      ( l1_pre_topc(sK0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_34,plain,
% 3.96/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3352,plain,
% 3.96/0.99      ( m1_pre_topc(X0_54,sK0) != iProver_top
% 3.96/0.99      | k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_2775,c_32,c_33,c_34,c_35,c_36,c_37,c_42,c_43]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3353,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(X0_54)) = k2_tmap_1(sK0,sK1,sK4,X0_54)
% 3.96/0.99      | m1_pre_topc(X0_54,sK0) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_3352]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3360,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK3)) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1348,c_3353]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3562,plain,
% 3.96/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3)
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_3528,c_3360]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_41,plain,
% 3.96/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_16,plain,
% 3.96/0.99      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_46,plain,
% 3.96/0.99      ( m1_pre_topc(X0,X0) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_48,plain,
% 3.96/0.99      ( m1_pre_topc(sK0,sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7538,plain,
% 3.96/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK3,sK4) = k2_tmap_1(sK0,sK1,sK4,sK3) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3562,c_32,c_33,c_34,c_41,c_48]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_24,negated_conjecture,
% 3.96/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_725,negated_conjecture,
% 3.96/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1350,plain,
% 3.96/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_725]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3529,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k3_tmap_1(sK0,sK1,sK0,sK2,sK4)
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1350,c_3516]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3361,plain,
% 3.96/0.99      ( k2_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),sK4,u1_struct_0(sK2)) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1350,c_3353]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3549,plain,
% 3.96/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2)
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK0,sK0) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_3529,c_3361]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_39,plain,
% 3.96/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7244,plain,
% 3.96/0.99      ( k3_tmap_1(sK0,sK1,sK0,sK2,sK4) = k2_tmap_1(sK0,sK1,sK4,sK2) ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3549,c_32,c_33,c_34,c_39,c_48]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_21,negated_conjecture,
% 3.96/0.99      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 3.96/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_728,negated_conjecture,
% 3.96/0.99      ( k1_tsep_1(sK0,sK2,sK3) = sK0 ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_15,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3),X4,k10_tmap_1(X0,X3,X1,X2,k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X1,X4),k3_tmap_1(X0,X3,k1_tsep_1(X0,X1,X2),X2,X4)))
% 3.96/0.99      | ~ v1_funct_2(X4,u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))
% 3.96/0.99      | ~ m1_pre_topc(X2,X0)
% 3.96/0.99      | ~ m1_pre_topc(X1,X0)
% 3.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0,X1,X2)),u1_struct_0(X3))))
% 3.96/0.99      | ~ v2_pre_topc(X3)
% 3.96/0.99      | ~ v2_pre_topc(X0)
% 3.96/0.99      | v2_struct_0(X0)
% 3.96/0.99      | v2_struct_0(X3)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | v2_struct_0(X1)
% 3.96/0.99      | ~ l1_pre_topc(X0)
% 3.96/0.99      | ~ l1_pre_topc(X3)
% 3.96/0.99      | ~ v1_funct_1(X4) ),
% 3.96/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_733,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52)))
% 3.96/0.99      | ~ v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X0_54)
% 3.96/0.99      | ~ m1_pre_topc(X1_54,X0_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54))))
% 3.96/0.99      | ~ v2_pre_topc(X3_54)
% 3.96/0.99      | ~ v2_pre_topc(X0_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(X3_54)
% 3.96/0.99      | v2_struct_0(X2_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X0_54)
% 3.96/0.99      | ~ l1_pre_topc(X3_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1343,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54),X0_52,k10_tmap_1(X0_54,X3_54,X1_54,X2_54,k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X1_54,X0_52),k3_tmap_1(X0_54,X3_54,k1_tsep_1(X0_54,X1_54,X2_54),X2_54,X0_52))) = iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X0_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X1_54,X0_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X0_54,X1_54,X2_54)),u1_struct_0(X3_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_733]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3258,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(sK3) = iProver_top
% 3.96/0.99      | v2_struct_0(sK2) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_728,c_1343]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3261,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(sK3) = iProver_top
% 3.96/0.99      | v2_struct_0(sK2) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_3258,c_728]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_25,negated_conjecture,
% 3.96/0.99      ( ~ v2_struct_0(sK2) ),
% 3.96/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_38,plain,
% 3.96/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_23,negated_conjecture,
% 3.96/0.99      ( ~ v2_struct_0(sK3) ),
% 3.96/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_40,plain,
% 3.96/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3338,plain,
% 3.96/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3261,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3339,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(X0_54),X0_52,k10_tmap_1(sK0,X0_54,sK2,sK3,k3_tmap_1(sK0,X0_54,sK0,sK2,X0_52),k3_tmap_1(sK0,X0_54,sK0,sK3,X0_52))) = iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_3338]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7284,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_7244,c_3339]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_44,plain,
% 3.96/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7388,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) = iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_7284,c_35,c_36,c_37,c_42,c_43,c_44]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7542,plain,
% 3.96/0.99      ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_7538,c_7388]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_pre_topc(X4,X5)
% 3.96/0.99      | ~ m1_pre_topc(X1,X5)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.96/0.99      | m1_subset_1(k10_tmap_1(X5,X2,X1,X4,X0,X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))))
% 3.96/0.99      | ~ v2_pre_topc(X2)
% 3.96/0.99      | ~ v2_pre_topc(X5)
% 3.96/0.99      | v2_struct_0(X5)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | v2_struct_0(X4)
% 3.96/0.99      | v2_struct_0(X1)
% 3.96/0.99      | ~ l1_pre_topc(X5)
% 3.96/0.99      | ~ l1_pre_topc(X2)
% 3.96/0.99      | ~ v1_funct_1(X3)
% 3.96/0.99      | ~ v1_funct_1(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_739,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X3_54)
% 3.96/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.96/0.99      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ v2_pre_topc(X3_54)
% 3.96/0.99      | ~ v2_pre_topc(X1_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(X3_54)
% 3.96/0.99      | v2_struct_0(X2_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X3_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | ~ v1_funct_1(X1_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1337,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)))) = iProver_top
% 3.96/0.99      | v2_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3819,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(sK3) = iProver_top
% 3.96/0.99      | v2_struct_0(sK2) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_728,c_1337]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4218,plain,
% 3.96/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_3819,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4219,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_54)))) = iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_4218]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1,plain,
% 3.96/0.99      ( ~ r2_funct_2(X0,X1,X2,X3)
% 3.96/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.96/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.96/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.96/0.99      | ~ v1_funct_1(X3)
% 3.96/0.99      | ~ v1_funct_1(X2)
% 3.96/0.99      | X2 = X3 ),
% 3.96/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_744,plain,
% 3.96/0.99      ( ~ r2_funct_2(X0_53,X1_53,X0_52,X1_52)
% 3.96/0.99      | ~ v1_funct_2(X1_52,X0_53,X1_53)
% 3.96/0.99      | ~ v1_funct_2(X0_52,X0_53,X1_53)
% 3.96/0.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | ~ v1_funct_1(X1_52)
% 3.96/0.99      | X0_52 = X1_52 ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1332,plain,
% 3.96/0.99      ( X0_52 = X1_52
% 3.96/0.99      | r2_funct_2(X0_53,X1_53,X0_52,X1_52) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,X0_53,X1_53) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2269,plain,
% 3.96/0.99      ( sK4 = X0_52
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1345,c_1332]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2650,plain,
% 3.96/0.99      ( v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | sK4 = X0_52
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_2269,c_42,c_43]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2651,plain,
% 3.96/0.99      ( sK4 = X0_52
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,X0_52) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_2650]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4241,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_4219,c_2651]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4908,plain,
% 3.96/0.99      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_4241,c_35,c_36,c_37]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4909,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52) = sK4
% 3.96/0.99      | r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,X0_52,X1_52)) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_4908]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8275,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_7542,c_4909]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2,plain,
% 3.96/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_86,plain,
% 3.96/0.99      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_88,plain,
% 3.96/0.99      ( l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) = iProver_top ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_86]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_743,plain,
% 3.96/0.99      ( ~ l1_pre_topc(X0_54) | l1_struct_0(X0_54) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2059,plain,
% 3.96/0.99      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_743]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2060,plain,
% 3.96/0.99      ( l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2059]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_11,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_pre_topc(X4,X5)
% 3.96/0.99      | ~ m1_pre_topc(X1,X5)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.96/0.99      | ~ v2_pre_topc(X2)
% 3.96/0.99      | ~ v2_pre_topc(X5)
% 3.96/0.99      | v2_struct_0(X5)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | v2_struct_0(X4)
% 3.96/0.99      | v2_struct_0(X1)
% 3.96/0.99      | ~ l1_pre_topc(X5)
% 3.96/0.99      | ~ l1_pre_topc(X2)
% 3.96/0.99      | ~ v1_funct_1(X3)
% 3.96/0.99      | ~ v1_funct_1(X0)
% 3.96/0.99      | v1_funct_1(k10_tmap_1(X5,X2,X1,X4,X0,X3)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_737,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X3_54)
% 3.96/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ v2_pre_topc(X3_54)
% 3.96/0.99      | ~ v2_pre_topc(X1_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(X3_54)
% 3.96/0.99      | v2_struct_0(X2_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X3_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | ~ v1_funct_1(X1_52)
% 3.96/0.99      | v1_funct_1(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52)) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_11]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1828,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X1_54),u1_struct_0(X1_54),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_pre_topc(X0_54,X2_54)
% 3.96/0.99      | ~ m1_pre_topc(X1_54,X2_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,X1_54),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1_54),u1_struct_0(sK1))))
% 3.96/0.99      | ~ v2_pre_topc(X2_54)
% 3.96/0.99      | ~ v2_pre_topc(sK1)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | v2_struct_0(X2_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(sK1)
% 3.96/0.99      | ~ l1_pre_topc(X2_54)
% 3.96/0.99      | ~ l1_pre_topc(sK1)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | v1_funct_1(k10_tmap_1(X2_54,sK1,X1_54,X0_54,k2_tmap_1(sK0,sK1,sK4,X1_54),X0_52))
% 3.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X1_54)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_737]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2440,plain,
% 3.96/0.99      ( ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.96/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 3.96/0.99      | ~ v2_pre_topc(sK1)
% 3.96/0.99      | ~ v2_pre_topc(sK0)
% 3.96/0.99      | v2_struct_0(sK3)
% 3.96/0.99      | v2_struct_0(sK2)
% 3.96/0.99      | v2_struct_0(sK1)
% 3.96/0.99      | v2_struct_0(sK0)
% 3.96/0.99      | ~ l1_pre_topc(sK1)
% 3.96/0.99      | ~ l1_pre_topc(sK0)
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.96/0.99      | ~ v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1828]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2441,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(sK3) = iProver_top
% 3.96/0.99      | v2_struct_0(sK2) = iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2440]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_3,plain,
% 3.96/0.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_742,plain,
% 3.96/0.99      ( ~ m1_pre_topc(X0_54,X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | l1_pre_topc(X0_54) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1334,plain,
% 3.96/0.99      ( m1_pre_topc(X0_54,X1_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2356,plain,
% 3.96/0.99      ( l1_pre_topc(sK3) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1348,c_1334]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2487,plain,
% 3.96/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_2356,c_34]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1333,plain,
% 3.96/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_struct_0(X0_54) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2492,plain,
% 3.96/0.99      ( l1_struct_0(sK3) = iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2487,c_1333]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2357,plain,
% 3.96/0.99      ( l1_pre_topc(sK2) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1350,c_1334]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2557,plain,
% 3.96/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_2357,c_34]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2562,plain,
% 3.96/0.99      ( l1_struct_0(sK2) = iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_2557,c_1333]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_14,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ l1_struct_0(X1)
% 3.96/0.99      | ~ l1_struct_0(X3)
% 3.96/0.99      | ~ l1_struct_0(X2)
% 3.96/0.99      | ~ v1_funct_1(X0)
% 3.96/0.99      | v1_funct_1(k2_tmap_1(X1,X2,X0,X3)) ),
% 3.96/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_734,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(X1_54)
% 3.96/0.99      | ~ l1_struct_0(X2_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | v1_funct_1(k2_tmap_1(X0_54,X1_54,X0_52,X2_54)) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1764,plain,
% 3.96/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,X0_54))
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_734]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2745,plain,
% 3.96/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(sK3)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3))
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1764]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2746,plain,
% 3.96/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK3) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) = iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_2745]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4742,plain,
% 3.96/0.99      ( ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(sK2)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2))
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1764]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4743,plain,
% 3.96/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK2) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) = iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_4742]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_13,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | v1_funct_2(k2_tmap_1(X1,X2,X0,X3),u1_struct_0(X3),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ l1_struct_0(X1)
% 3.96/0.99      | ~ l1_struct_0(X3)
% 3.96/0.99      | ~ l1_struct_0(X2)
% 3.96/0.99      | ~ v1_funct_1(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_735,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | v1_funct_2(k2_tmap_1(X0_54,X1_54,X0_52,X2_54),u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(X1_54)
% 3.96/0.99      | ~ l1_struct_0(X2_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_13]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1769,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,X0_54),u1_struct_0(X0_54),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_735]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6226,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(sK3)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1769]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6227,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) = iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK3) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_6226]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_10,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.96/0.99      | ~ v1_funct_2(X3,u1_struct_0(X4),u1_struct_0(X2))
% 3.96/0.99      | v1_funct_2(k10_tmap_1(X5,X2,X1,X4,X0,X3),u1_struct_0(k1_tsep_1(X5,X1,X4)),u1_struct_0(X2))
% 3.96/0.99      | ~ m1_pre_topc(X4,X5)
% 3.96/0.99      | ~ m1_pre_topc(X1,X5)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.96/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
% 3.96/0.99      | ~ v2_pre_topc(X2)
% 3.96/0.99      | ~ v2_pre_topc(X5)
% 3.96/0.99      | v2_struct_0(X5)
% 3.96/0.99      | v2_struct_0(X2)
% 3.96/0.99      | v2_struct_0(X4)
% 3.96/0.99      | v2_struct_0(X1)
% 3.96/0.99      | ~ l1_pre_topc(X5)
% 3.96/0.99      | ~ l1_pre_topc(X2)
% 3.96/0.99      | ~ v1_funct_1(X3)
% 3.96/0.99      | ~ v1_funct_1(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_738,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54))
% 3.96/0.99      | ~ v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54))
% 3.96/0.99      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54))
% 3.96/0.99      | ~ m1_pre_topc(X2_54,X3_54)
% 3.96/0.99      | ~ m1_pre_topc(X0_54,X3_54)
% 3.96/0.99      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54))))
% 3.96/0.99      | ~ v2_pre_topc(X3_54)
% 3.96/0.99      | ~ v2_pre_topc(X1_54)
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | v2_struct_0(X3_54)
% 3.96/0.99      | v2_struct_0(X2_54)
% 3.96/0.99      | v2_struct_0(X1_54)
% 3.96/0.99      | ~ l1_pre_topc(X3_54)
% 3.96/0.99      | ~ l1_pre_topc(X1_54)
% 3.96/0.99      | ~ v1_funct_1(X0_52)
% 3.96/0.99      | ~ v1_funct_1(X1_52) ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1338,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(X0_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(X2_54),u1_struct_0(X1_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(X3_54,X1_54,X0_54,X2_54,X0_52,X1_52),u1_struct_0(k1_tsep_1(X3_54,X0_54,X2_54)),u1_struct_0(X1_54)) = iProver_top
% 3.96/0.99      | m1_pre_topc(X2_54,X3_54) != iProver_top
% 3.96/0.99      | m1_pre_topc(X0_54,X3_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2_54),u1_struct_0(X1_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X3_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X2_54) = iProver_top
% 3.96/0.99      | v2_struct_0(X1_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X3_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(X1_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4664,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 3.96/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.96/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v2_struct_0(sK3) = iProver_top
% 3.96/0.99      | v2_struct_0(sK2) = iProver_top
% 3.96/0.99      | v2_struct_0(sK0) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_728,c_1338]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4669,plain,
% 3.96/0.99      ( l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_4664,c_32,c_33,c_34,c_38,c_39,c_40,c_41]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4670,plain,
% 3.96/0.99      ( v1_funct_2(X0_52,u1_struct_0(sK3),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(X1_52,u1_struct_0(sK2),u1_struct_0(X0_54)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,X0_54,sK2,sK3,X1_52,X0_52),u1_struct_0(sK0),u1_struct_0(X0_54)) = iProver_top
% 3.96/0.99      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | m1_subset_1(X1_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X0_54)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | l1_pre_topc(X0_54) != iProver_top
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(X1_52) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_4669]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4924,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_3339,c_4909]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6265,plain,
% 3.96/0.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_4924,c_35,c_36,c_37,c_42,c_43,c_44]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6266,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_6265]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6278,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v2_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_pre_topc(sK1) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_4670,c_6266]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6281,plain,
% 3.96/0.99      ( m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_6278,c_35,c_36,c_37]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_6282,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k3_tmap_1(sK0,sK1,sK0,sK2,sK4),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK2,sK4)) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_6281]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7247,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK2)) != iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_7244,c_6282]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7395,plain,
% 3.96/0.99      ( v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_7247,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2562,
% 3.96/0.99                 c_4743]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7396,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) = sK4
% 3.96/0.99      | v1_funct_2(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k3_tmap_1(sK0,sK1,sK0,sK3,sK4))) != iProver_top
% 3.96/0.99      | v1_funct_1(k3_tmap_1(sK0,sK1,sK0,sK3,sK4)) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_7395]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_7541,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK3),u1_struct_0(sK3),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 3.96/0.99      | v1_funct_1(k2_tmap_1(sK0,sK1,sK4,sK3)) != iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_7538,c_7396]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8411,plain,
% 3.96/0.99      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_8275,c_32,c_33,c_34,c_35,c_36,c_37,c_38,c_39,c_40,
% 3.96/0.99                 c_41,c_42,c_43,c_44,c_88,c_2060,c_2441,c_2492,c_2562,
% 3.96/0.99                 c_2746,c_4743,c_6227,c_7541]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8412,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_8411]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8419,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK3) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1340,c_8412]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8885,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ l1_struct_0(sK2)
% 3.96/0.99      | ~ l1_struct_0(sK1)
% 3.96/0.99      | ~ l1_struct_0(sK0)
% 3.96/0.99      | ~ v1_funct_1(sK4) ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1769]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_8886,plain,
% 3.96/0.99      ( v1_funct_2(k2_tmap_1(sK0,sK1,sK4,sK2),u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK2) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_8885]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9364,plain,
% 3.96/0.99      ( m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_8419,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2492,
% 3.96/0.99                 c_2562,c_8886]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9365,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | m1_subset_1(k2_tmap_1(sK0,sK1,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_9364]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9370,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | l1_struct_0(sK2) != iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | l1_struct_0(sK0) != iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(superposition,[status(thm)],[c_1340,c_9365]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9515,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) = sK4 ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_9370,c_34,c_37,c_42,c_43,c_44,c_88,c_2060,c_2562]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_4,plain,
% 3.96/0.99      ( v2_struct_0(X0)
% 3.96/0.99      | ~ v1_xboole_0(u1_struct_0(X0))
% 3.96/0.99      | ~ l1_struct_0(X0) ),
% 3.96/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_5,plain,
% 3.96/0.99      ( r1_funct_2(X0,X1,X2,X3,X4,X4)
% 3.96/0.99      | ~ v1_funct_2(X4,X2,X3)
% 3.96/0.99      | ~ v1_funct_2(X4,X0,X1)
% 3.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.96/0.99      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.96/0.99      | v1_xboole_0(X1)
% 3.96/0.99      | v1_xboole_0(X3)
% 3.96/0.99      | ~ v1_funct_1(X4) ),
% 3.96/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_17,negated_conjecture,
% 3.96/0.99      ( ~ r1_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1),sK4,k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) ),
% 3.96/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_337,plain,
% 3.96/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.96/0.99      | ~ v1_funct_2(X0,X3,X4)
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.96/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.96/0.99      | v1_xboole_0(X2)
% 3.96/0.99      | v1_xboole_0(X4)
% 3.96/0.99      | ~ v1_funct_1(X0)
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0
% 3.96/0.99      | u1_struct_0(k1_tsep_1(sK0,sK2,sK3)) != X3
% 3.96/0.99      | u1_struct_0(sK1) != X4
% 3.96/0.99      | u1_struct_0(sK1) != X2
% 3.96/0.99      | u1_struct_0(sK0) != X1
% 3.96/0.99      | sK4 != X0 ),
% 3.96/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_338,plain,
% 3.96/0.99      ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | v1_xboole_0(u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | sK4 != k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) ),
% 3.96/0.99      inference(unflattening,[status(thm)],[c_337]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_370,plain,
% 3.96/0.99      ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | v2_struct_0(X0)
% 3.96/0.99      | ~ l1_struct_0(X0)
% 3.96/0.99      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | u1_struct_0(X0) != u1_struct_0(sK1) ),
% 3.96/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_338]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_717,plain,
% 3.96/0.99      ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | v2_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
% 3.96/0.99      inference(subtyping,[status(esa)],[c_370]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_747,plain,
% 3.96/0.99      ( ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))
% 3.96/0.99      | ~ v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1))))
% 3.96/0.99      | ~ m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.96/0.99      | ~ v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | sP0_iProver_split
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4 ),
% 3.96/0.99      inference(splitting,
% 3.96/0.99                [splitting(split),new_symbols(definition,[])],
% 3.96/0.99                [c_717]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1358,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK2,sK3)),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1654,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) != iProver_top
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(light_normalisation,[status(thm)],[c_1358,c_728]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_762,plain,
% 3.96/0.99      ( ~ v1_funct_1(X0_52) | v1_funct_1(X1_52) | X1_52 != X0_52 ),
% 3.96/0.99      theory(equality) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1738,plain,
% 3.96/0.99      ( ~ v1_funct_1(X0_52)
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)))
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52 ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_762]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1739,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != X0_52
% 3.96/0.99      | v1_funct_1(X0_52) != iProver_top
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_1738]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1741,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | v1_funct_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3))) = iProver_top
% 3.96/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.96/0.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2051,plain,
% 3.96/0.99      ( m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(global_propositional_subsumption,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_1654,c_42,c_1741]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2052,plain,
% 3.96/0.99      ( k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)) != sK4
% 3.96/0.99      | v1_funct_2(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(k10_tmap_1(sK0,sK1,sK2,sK3,k2_tmap_1(sK0,sK1,sK4,sK2),k2_tmap_1(sK0,sK1,sK4,sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(renaming,[status(thm)],[c_2051]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9519,plain,
% 3.96/0.99      ( sK4 != sK4
% 3.96/0.99      | v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(demodulation,[status(thm)],[c_9515,c_2052]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_9520,plain,
% 3.96/0.99      ( v1_funct_2(sK4,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.96/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.96/0.99      | sP0_iProver_split = iProver_top ),
% 3.96/0.99      inference(equality_resolution_simp,[status(thm)],[c_9519]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_746,plain,
% 3.96/0.99      ( v2_struct_0(X0_54)
% 3.96/0.99      | ~ l1_struct_0(X0_54)
% 3.96/0.99      | u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.96/0.99      | ~ sP0_iProver_split ),
% 3.96/0.99      inference(splitting,
% 3.96/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.96/0.99                [c_717]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_1359,plain,
% 3.96/0.99      ( u1_struct_0(X0_54) != u1_struct_0(sK1)
% 3.96/0.99      | v2_struct_0(X0_54) = iProver_top
% 3.96/0.99      | l1_struct_0(X0_54) != iProver_top
% 3.96/0.99      | sP0_iProver_split != iProver_top ),
% 3.96/0.99      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(c_2138,plain,
% 3.96/0.99      ( v2_struct_0(sK1) = iProver_top
% 3.96/0.99      | l1_struct_0(sK1) != iProver_top
% 3.96/0.99      | sP0_iProver_split != iProver_top ),
% 3.96/0.99      inference(equality_resolution,[status(thm)],[c_1359]) ).
% 3.96/0.99  
% 3.96/0.99  cnf(contradiction,plain,
% 3.96/0.99      ( $false ),
% 3.96/0.99      inference(minisat,
% 3.96/0.99                [status(thm)],
% 3.96/0.99                [c_9520,c_2138,c_2060,c_44,c_43,c_37,c_35]) ).
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.96/0.99  
% 3.96/0.99  ------                               Statistics
% 3.96/0.99  
% 3.96/0.99  ------ General
% 3.96/0.99  
% 3.96/0.99  abstr_ref_over_cycles:                  0
% 3.96/0.99  abstr_ref_under_cycles:                 0
% 3.96/0.99  gc_basic_clause_elim:                   0
% 3.96/0.99  forced_gc_time:                         0
% 3.96/0.99  parsing_time:                           0.013
% 3.96/0.99  unif_index_cands_time:                  0.
% 3.96/0.99  unif_index_add_time:                    0.
% 3.96/0.99  orderings_time:                         0.
% 3.96/0.99  out_proof_time:                         0.023
% 3.96/0.99  total_time:                             0.409
% 3.96/0.99  num_of_symbols:                         58
% 3.96/0.99  num_of_terms:                           11487
% 3.96/0.99  
% 3.96/0.99  ------ Preprocessing
% 3.96/0.99  
% 3.96/0.99  num_of_splits:                          1
% 3.96/0.99  num_of_split_atoms:                     1
% 3.96/0.99  num_of_reused_defs:                     0
% 3.96/0.99  num_eq_ax_congr_red:                    21
% 3.96/0.99  num_of_sem_filtered_clauses:            1
% 3.96/0.99  num_of_subtypes:                        5
% 3.96/0.99  monotx_restored_types:                  0
% 3.96/0.99  sat_num_of_epr_types:                   0
% 3.96/0.99  sat_num_of_non_cyclic_types:            0
% 3.96/0.99  sat_guarded_non_collapsed_types:        1
% 3.96/0.99  num_pure_diseq_elim:                    0
% 3.96/0.99  simp_replaced_by:                       0
% 3.96/0.99  res_preprocessed:                       170
% 3.96/0.99  prep_upred:                             0
% 3.96/0.99  prep_unflattend:                        27
% 3.96/0.99  smt_new_axioms:                         0
% 3.96/0.99  pred_elim_cands:                        9
% 3.96/0.99  pred_elim:                              2
% 3.96/0.99  pred_elim_cl:                           3
% 3.96/0.99  pred_elim_cycles:                       4
% 3.96/0.99  merged_defs:                            0
% 3.96/0.99  merged_defs_ncl:                        0
% 3.96/0.99  bin_hyper_res:                          0
% 3.96/0.99  prep_cycles:                            4
% 3.96/0.99  pred_elim_time:                         0.011
% 3.96/0.99  splitting_time:                         0.
% 3.96/0.99  sem_filter_time:                        0.
% 3.96/0.99  monotx_time:                            0.
% 3.96/0.99  subtype_inf_time:                       0.001
% 3.96/0.99  
% 3.96/0.99  ------ Problem properties
% 3.96/0.99  
% 3.96/0.99  clauses:                                30
% 3.96/0.99  conjectures:                            14
% 3.96/0.99  epr:                                    14
% 3.96/0.99  horn:                                   24
% 3.96/0.99  ground:                                 15
% 3.96/0.99  unary:                                  14
% 3.96/0.99  binary:                                 2
% 3.96/0.99  lits:                                   154
% 3.96/0.99  lits_eq:                                6
% 3.96/0.99  fd_pure:                                0
% 3.96/0.99  fd_pseudo:                              0
% 3.96/0.99  fd_cond:                                0
% 3.96/0.99  fd_pseudo_cond:                         1
% 3.96/0.99  ac_symbols:                             0
% 3.96/0.99  
% 3.96/0.99  ------ Propositional Solver
% 3.96/0.99  
% 3.96/0.99  prop_solver_calls:                      30
% 3.96/0.99  prop_fast_solver_calls:                 3012
% 3.96/0.99  smt_solver_calls:                       0
% 3.96/0.99  smt_fast_solver_calls:                  0
% 3.96/0.99  prop_num_of_clauses:                    2468
% 3.96/0.99  prop_preprocess_simplified:             7723
% 3.96/0.99  prop_fo_subsumed:                       188
% 3.96/0.99  prop_solver_time:                       0.
% 3.96/0.99  smt_solver_time:                        0.
% 3.96/0.99  smt_fast_solver_time:                   0.
% 3.96/0.99  prop_fast_solver_time:                  0.
% 3.96/0.99  prop_unsat_core_time:                   0.
% 3.96/0.99  
% 3.96/0.99  ------ QBF
% 3.96/0.99  
% 3.96/0.99  qbf_q_res:                              0
% 3.96/0.99  qbf_num_tautologies:                    0
% 3.96/0.99  qbf_prep_cycles:                        0
% 3.96/0.99  
% 3.96/0.99  ------ BMC1
% 3.96/0.99  
% 3.96/0.99  bmc1_current_bound:                     -1
% 3.96/0.99  bmc1_last_solved_bound:                 -1
% 3.96/0.99  bmc1_unsat_core_size:                   -1
% 3.96/0.99  bmc1_unsat_core_parents_size:           -1
% 3.96/0.99  bmc1_merge_next_fun:                    0
% 3.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.96/0.99  
% 3.96/0.99  ------ Instantiation
% 3.96/0.99  
% 3.96/0.99  inst_num_of_clauses:                    812
% 3.96/0.99  inst_num_in_passive:                    227
% 3.96/0.99  inst_num_in_active:                     496
% 3.96/0.99  inst_num_in_unprocessed:                89
% 3.96/0.99  inst_num_of_loops:                      520
% 3.96/0.99  inst_num_of_learning_restarts:          0
% 3.96/0.99  inst_num_moves_active_passive:          19
% 3.96/0.99  inst_lit_activity:                      0
% 3.96/0.99  inst_lit_activity_moves:                0
% 3.96/0.99  inst_num_tautologies:                   0
% 3.96/0.99  inst_num_prop_implied:                  0
% 3.96/0.99  inst_num_existing_simplified:           0
% 3.96/0.99  inst_num_eq_res_simplified:             0
% 3.96/0.99  inst_num_child_elim:                    0
% 3.96/0.99  inst_num_of_dismatching_blockings:      897
% 3.96/0.99  inst_num_of_non_proper_insts:           1123
% 3.96/0.99  inst_num_of_duplicates:                 0
% 3.96/0.99  inst_inst_num_from_inst_to_res:         0
% 3.96/0.99  inst_dismatching_checking_time:         0.
% 3.96/0.99  
% 3.96/0.99  ------ Resolution
% 3.96/0.99  
% 3.96/0.99  res_num_of_clauses:                     0
% 3.96/0.99  res_num_in_passive:                     0
% 3.96/0.99  res_num_in_active:                      0
% 3.96/0.99  res_num_of_loops:                       174
% 3.96/0.99  res_forward_subset_subsumed:            62
% 3.96/0.99  res_backward_subset_subsumed:           0
% 3.96/0.99  res_forward_subsumed:                   0
% 3.96/0.99  res_backward_subsumed:                  0
% 3.96/0.99  res_forward_subsumption_resolution:     0
% 3.96/0.99  res_backward_subsumption_resolution:    0
% 3.96/0.99  res_clause_to_clause_subsumption:       657
% 3.96/0.99  res_orphan_elimination:                 0
% 3.96/0.99  res_tautology_del:                      148
% 3.96/0.99  res_num_eq_res_simplified:              0
% 3.96/0.99  res_num_sel_changes:                    0
% 3.96/0.99  res_moves_from_active_to_pass:          0
% 3.96/0.99  
% 3.96/0.99  ------ Superposition
% 3.96/0.99  
% 3.96/0.99  sup_time_total:                         0.
% 3.96/0.99  sup_time_generating:                    0.
% 3.96/0.99  sup_time_sim_full:                      0.
% 3.96/0.99  sup_time_sim_immed:                     0.
% 3.96/0.99  
% 3.96/0.99  sup_num_of_clauses:                     120
% 3.96/0.99  sup_num_in_active:                      94
% 3.96/0.99  sup_num_in_passive:                     26
% 3.96/0.99  sup_num_of_loops:                       102
% 3.96/0.99  sup_fw_superposition:                   69
% 3.96/0.99  sup_bw_superposition:                   32
% 3.96/0.99  sup_immediate_simplified:               15
% 3.96/0.99  sup_given_eliminated:                   0
% 3.96/0.99  comparisons_done:                       0
% 3.96/0.99  comparisons_avoided:                    0
% 3.96/0.99  
% 3.96/0.99  ------ Simplifications
% 3.96/0.99  
% 3.96/0.99  
% 3.96/0.99  sim_fw_subset_subsumed:                 1
% 3.96/0.99  sim_bw_subset_subsumed:                 3
% 3.96/0.99  sim_fw_subsumed:                        0
% 3.96/0.99  sim_bw_subsumed:                        1
% 3.96/0.99  sim_fw_subsumption_res:                 20
% 3.96/0.99  sim_bw_subsumption_res:                 0
% 3.96/0.99  sim_tautology_del:                      1
% 3.96/0.99  sim_eq_tautology_del:                   3
% 3.96/0.99  sim_eq_res_simp:                        1
% 3.96/0.99  sim_fw_demodulated:                     0
% 3.96/0.99  sim_bw_demodulated:                     6
% 3.96/0.99  sim_light_normalised:                   14
% 3.96/0.99  sim_joinable_taut:                      0
% 3.96/0.99  sim_joinable_simp:                      0
% 3.96/0.99  sim_ac_normalised:                      0
% 3.96/0.99  sim_smt_subsumption:                    0
% 3.96/0.99  
%------------------------------------------------------------------------------
